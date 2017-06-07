package edu.ucsc.soe.reductionist;

import automata.AutomataException;
import automata.svpa.*;
import org.roaringbitmap.RoaringBitmap;
import org.sat4j.specs.TimeoutException;
import theory.svpa.equalityalgebra.EqualityAlgebra;
import theory.svpa.equalityalgebra.EqualityPredicate;
import theory.svpa.equalityalgebra.UnaryPredicate;

import javax.json.*;
import java.io.FileReader;
import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

//import sometheory

public class Reductionist {
    public static void main(String[] args) {
    }

    protected static class ProdID {
        public String name;
        public int id;
        public RoaringBitmap mask;
    }
    protected static class Production {
        public ProdID id;
        public ProdID getId() { return id; }
        public Production(String s) {
            this.id = new ProdID();
            this.id.name = s;
        }
    }
    protected static class NonTerminal extends Production {
        public List<ProdID> tags;
        public RoaringBitmap mask;
        public List<List<Production>> rules;
        public NonTerminal(String n) {
            super(n);
            this.tags = new ArrayList<>();
            this.rules = new ArrayList<>();
        }
    }
    protected static class Terminal extends Production {
        public Terminal(String n) {
            super(n);
        }
    }

    protected enum RefType {
        Open,
        ByIdStart,
        ByIdEnd,
        Specific,
        SpecificCall,
        SpecificReturn
    }
    protected static class StateRef {
        public RefType type;
        public Integer specific;
        public ProdID byId;
        //only for ends/returns
        public Integer caller;
        public static StateRef MkOpen() {
            StateRef r = new StateRef();
            r.type = RefType.Open;
            return r;
        }
        public static StateRef MkSpecific(Integer stateId) {
            StateRef r = new StateRef();
            r.type = RefType.Specific;
            r.specific = stateId;
            return r;
        }
        public static StateRef MkStart(ProdID prod) {
            StateRef r = new StateRef();
            r.type = RefType.ByIdStart;
            r.byId = prod;
            return r;
        }
        public static StateRef MkEnd(ProdID prod, Integer caller) {
            StateRef r = new StateRef();
            r.type = RefType.ByIdEnd;
            r.byId = prod;
            r.caller = caller;
            return r;
        }
        public static StateRef MkSpecificCall(Integer s, ProdID prod) {
            StateRef r = new StateRef();
            r.type = RefType.SpecificCall;
            r.specific = s;
            r.byId = prod;
            return r;
        }
        public static StateRef MkSpecificReturn(Integer s, ProdID prod, Integer caller) {
            StateRef r = new StateRef();
            r.type = RefType.SpecificReturn;
            r.specific = s;
            r.byId = prod;
            r.caller = caller;
            return r;
        }
        protected StateRef() {}
    }
    protected static class Frag {
        // A source, a ProdID, and a target
        // Source may be stateID or ? or end(NT), target may be stateID or ? or start(NT)
        public StateRef source, target;
        public RoaringBitmap symbol;
        public Frag(StateRef src, RoaringBitmap symb, StateRef tgt) {
            this.source = src;
            this.symbol = symb;
            this.target = tgt;
        }
    }

    // also add a new function to make an EM-automaton from a grammar:
    //  * for each NT find out if that NT has tags or descendants with tags
    //  * ignore all terminals
    //  * when constructing automaton, skip any calls to NTs that don't have tags or descendants with tags

    public static Reductionist fromJSONFile(String path, boolean emsOnly)
        throws java.io.IOException,
            automata.AutomataException,
            org.sat4j.specs.TimeoutException {
        FileReader fread = new FileReader(path);
        JsonReader jread = Json.createReader(fread);
        JsonObject jobj = jread.readObject();

        JsonObject nts = jobj.getJsonObject("nonterminals");

        HashMap<String, NonTerminal> nonterminals = new HashMap<>();
        NonTerminal root = new NonTerminal(" root");
        nonterminals.put(root.id.name, root);
        HashMap<String, Terminal> terminals = new HashMap<>();
        HashMap<String, ProdID> tags = new HashMap<>();

        // Find every nonterminal, terminal, and tag.
        // Also note which nonterminals are used.
        // Also introduce a new terminal for every rule to obtain an
        // unambiguous, deterministic SVPA.
        HashSet<String> usedNTs = new HashSet<>();
        for(Map.Entry<String, JsonValue> entry : nts.entrySet()) {
            JsonObject prodObj = (JsonObject)entry.getValue();
            NonTerminal nt = new NonTerminal(entry.getKey());
            nonterminals.put(nt.id.name, nt);
            boolean hasTags = false;
            JsonValue markup = prodObj.get("markup");
            if(markup != null && markup != JsonValue.NULL) {
                for(Map.Entry<String, JsonValue> markupTags : ((JsonObject)markup).entrySet()) {
                    for(JsonValue tagValue : (JsonArray)markupTags.getValue()) {
                        String tagString = "NULL";
                        if(tagValue != null && tagValue != JsonValue.NULL) {
                            tagString = ((JsonString)tagValue).getString();
                        }
                        String tag = markupTags.getKey() + "#:#" + tagString;
                        if(tags.containsKey(tag)) {
                            nt.tags.add(tags.get(tag));
                        } else {
                            ProdID tagProd = new ProdID();
                            tagProd.name = tag;
                            tags.put(tag,tagProd);
                            nt.tags.add(tagProd);
                        }
                    }
                }
            }

            int ruleNumber = 0;
            for(JsonValue ruleVal : prodObj.getJsonArray("rules")) {
                JsonObject rule = (JsonObject)ruleVal;
                String key = String.format("$R%d", ruleNumber++);
                if(!terminals.containsKey(key)) {
                    terminals.put(key, new Terminal(key));
                }
                JsonArray expansion = rule.getJsonArray("expansion");
                for(JsonValue js : expansion) {
                    String s = ((JsonString)js).getString();
                    int slen = s.length();
                    if(s.charAt(0) == '[' && s.charAt(1) == '['
                       && s.charAt(slen-2) == ']' && s.charAt(slen-1) == ']') {
                        // I'm a nonterminal reference, note that I'm referenced
                        // Can't necessarily resolve me yet, so just keep going.
                        String refProdName = s.substring(2, slen-2);
                        usedNTs.add(refProdName);
                    } else {
                        // I'm a terminal reference, add me to terminals
                        if(!terminals.containsKey(s)) {
                            terminals.put(s, new Terminal(s));
                        }
                    }
                }
            }
        }
        for(int i = 0; i < nonterminals.size() - usedNTs.size(); i++) {
            String rootKey = String.format("$Root%d", i);
            terminals.put(rootKey, new Terminal(rootKey));
        }

        // Now we can build a universe.  Terminals, then nonterminals, then tags.
        long terminalCount = terminals.size();
        long nonterminalCount = nonterminals.size();
        long tagCount = tags.size();
        RoaringBitmap universe = new RoaringBitmap();
        universe.add(0L, terminalCount + nonterminalCount + tagCount);
        RoaringBitmap terminalMask = new RoaringBitmap();
        terminalMask.add(0L, terminalCount);
        RoaringBitmap nonterminalMask = new RoaringBitmap();
        nonterminalMask.add(terminalCount, terminalCount + nonterminalCount);
        RoaringBitmap tagMask = new RoaringBitmap();
        tagMask.add(terminalCount+nonterminalCount, terminalCount+nonterminalCount+tagCount);

        // Number every terminal, nonterminal, and tag!

        Terminal[] sortedTerminals = terminals.keySet().stream().
            sorted().map(terminals::get).toArray(Terminal[]::new);
        NonTerminal[] sortedNonTerminals = nonterminals.keySet().stream().
            sorted().map(nonterminals::get).toArray(NonTerminal[]::new);
        ProdID[] sortedTags = tags.keySet().stream().
            sorted().map(tags::get).toArray(ProdID[]::new);
        for(int i = 0; i < sortedTerminals.length; i++) {
            sortedTerminals[i].id.id = i;
            sortedTerminals[i].id.mask = RoaringBitmap.bitmapOf(i);
        }
        for(int i = 0; i < sortedTags.length; i++) {
            // TODO: Definitely a risk of overflow, but only for massive grammars
            int id = (int)(i + terminalCount + nonterminalCount);
            sortedTags[i].id = id;
            // TODO: could also store the "type" of the markup in this mask?
            sortedTags[i].mask = RoaringBitmap.bitmapOf(id);
        }
//        ProdID[] sortedNonTerminalReturns = new ProdID[sortedNonTerminals.length];
        for(int i = 0; i < sortedNonTerminals.length; i++) {
            NonTerminal nt = sortedNonTerminals[i];
            int id = (int)(i + terminalCount);
            //System.out.println(nt.id.name+":"+id);
            nt.id.id = id;
            nt.id.mask = RoaringBitmap.bitmapOf(id);
            nt.mask = RoaringBitmap.bitmapOf(id);
            for(ProdID tag : nt.tags) {
                nt.mask.or(tag.mask);
            }

//            ProdID retID = new ProdID();
//            long retIdx = terminalCount + nonterminalCount + tagCount + i;
//            retID.name = nt.id.name;
//            retID.mask = RoaringBitmap.bitmapOf((int)retIdx);
//            retID.id = (int)retIdx;
//            sortedNonTerminalReturns[i] = retID;
        }
        Stream<ProdID> terminalIDs = Arrays.stream(sortedTerminals).
                map(Production::getId);
        Stream<ProdID> nonterminalIDs = Arrays.stream(sortedNonTerminals).
                map(Production::getId);
        Stream<ProdID> tagIDs = Arrays.stream(sortedTags);
        List<ProdID> productions = Stream.concat(
                Stream.concat(terminalIDs, nonterminalIDs),
                tagIDs
        ).collect(Collectors.toList());

        // Now hook up references and add any un-referenced rules to the root nonterminal.
        for(Map.Entry<String, JsonValue> entry : nts.entrySet()) {
            JsonObject prodObj = (JsonObject)entry.getValue();
            NonTerminal nt = nonterminals.get(entry.getKey());
            int ruleNumber = 0;
            for(JsonValue ruleVal : prodObj.getJsonArray("rules")) {
                JsonObject rule = (JsonObject)ruleVal;
                // TODO: ignoring app_rate
                ArrayList<Production> steps = new ArrayList<>();
                String key = String.format("$R%d", ruleNumber++);
                steps.add(terminals.get(key));
                JsonArray expansion = rule.getJsonArray("expansion");
                for(JsonValue js : expansion) {
                    String s = ((JsonString)js).getString();
                    int slen = s.length();
                    if(s.charAt(0) == '[' && s.charAt(1) == '['
                       && s.charAt(slen-2) == ']' && s.charAt(slen-1) == ']') {
                        // I'm a nonterminal reference
                        String refProdName = s.substring(2, slen-2);
                        steps.add(nonterminals.get(refProdName));
                    } else if(!emsOnly) {
                        steps.add(terminals.get(s));
                    }
                }
                nt.rules.add(steps);
            }
            if(!usedNTs.contains(nt.id.name)) {
                ArrayList<Production> rootSteps = new ArrayList<>();
                String key = String.format("$Root%d", root.rules.size());
                rootSteps.add(terminals.get(key));
                rootSteps.add(nt);
                root.rules.add(rootSteps);
            }
        }

        HashMap<String, Boolean> hasTagsStar = new HashMap<>();
        fillEMsClosure(root, hasTagsStar);

        System.out.format("Ts:%d, NTs:%d, tags:%d%n", terminalCount, nonterminalCount, tagCount);
        System.out.format("RN:%s, %d, %d%n", root.id.name, root.id.id, root.rules.size());


        FiniteSetSolver unaryTheory = new FiniteSetSolver(
                terminalCount + nonterminalCount + tagCount,
                terminalCount+nonterminalCount
        );

        // Now build frags for each nonterminal
        int stateCount = 0;
        Map<Integer, Integer> ntStarts = new HashMap<>();
        Map<Integer, Integer> ntEnds = new HashMap<>();
        List<Frag> openEdges = new ArrayList<>();
        List<Frag> edges = new ArrayList<>();
        for(NonTerminal nt : sortedNonTerminals) {
            if(emsOnly && !hasTagsStar.get(nt.getId().name)) {
                continue;
            }
            // Allocate start and end states, tie to this NT ID
            int startState = stateCount++;
            int endState = stateCount++;
            ntStarts.put(nt.id.id, startState);
            ntEnds.put(nt.id.id, endState);
            boolean anyRulesInteresting = !emsOnly;
            // Create frags for all edges of all productions, including call edges
            for(List<Production> steps : nt.rules) {
                System.out.println(steps.get(0).getId().name);
                if(emsOnly) {
                    boolean anyInteresting = false;
                    for(Production prod : steps) {
                        if((prod instanceof NonTerminal) && hasTagsStar.get(((NonTerminal)prod).getId().name)) {
                            anyInteresting = true;
                            anyRulesInteresting = true;
                        }
                    }
                    if(!anyInteresting) {
                        continue;
                    }
                }
                int here = startState;
                Frag active = null;
                for(Production prod : steps) {
                    if(emsOnly && prod instanceof NonTerminal) {
                        if (!hasTagsStar.get(((NonTerminal)prod).getId().name)) {
                            continue;
                        }
                    }
                    if(active != null) {
                        here = stateCount++;
                        System.out.format("Link frag ->%d%n", here);
                        active.target = StateRef.MkSpecific(here);
                    }
                    if(prod instanceof Terminal) {
                        active = new Frag(
                                StateRef.MkSpecific(here),
                                prod.id.mask,
                                StateRef.MkOpen()
                        );
                        System.out.format("Open frag %d->%n", here);
                        edges.add(active);
                    } else if(prod instanceof NonTerminal) {
                        active = new Frag(
                                StateRef.MkSpecific(here), // Gonna turn into a CallMove
                                ((NonTerminal)prod).mask,
                                StateRef.MkStart(prod.id)
                        );
                        System.out.format("Link in-frag %d->%s%n", here, prod.id.name);
                        edges.add(active);
                        openEdges.add(active);
                        // ... implicitly some other stuff happens, then...
                        active = new Frag(
                                StateRef.MkEnd(prod.id, here), // Gonna turn into a ReturnMove
                                prod.id.mask,
                                StateRef.MkOpen()
                        );
                        System.out.format("Link out-frag %s->%n",prod.id.name);
                        edges.add(active);
                        openEdges.add(active);
                    } else {
                        throw new IllegalArgumentException("Rules may only contain terminals and nonterminals");
                    }
                }
                System.out.format("Link end frag ->%d%n", endState);
                active.target = StateRef.MkSpecific(endState);
            }
            if(!anyRulesInteresting) {
                ntEnds.put(nt.id.id, startState);
            }
        }

        // Hook up open frags along starts/ends.  Not really necessary I guess
        for(Frag f : openEdges) {
            if(f.target.type == RefType.ByIdStart) {
                f.target = StateRef.MkSpecificCall(ntStarts.get(f.target.byId.id), f.target.byId);
            } else if(f.source.type == RefType.ByIdEnd) {
                f.source = StateRef.MkSpecificReturn(ntEnds.get(f.source.byId.id), f.source.byId, f.source.caller);
            } else {
                throw new IllegalArgumentException("Messed up fragment, should never happen");
            }
        }

        int initial = stateCount++;
        int terminal = stateCount++;

        int rootStart = ntStarts.get(root.id.id);
        int rootEnd = ntEnds.get(root.id.id);
        edges.add(new Frag(
                StateRef.MkSpecific(initial),
                root.mask, // Gonna turn into a CallMove
                StateRef.MkSpecificCall(rootStart, root.id)
        ));
        edges.add(new Frag(
                StateRef.MkSpecificReturn(rootEnd, root.id, initial),
                root.id.mask,
                StateRef.MkSpecific(terminal)
        ));
        List<SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>> moves = new ArrayList<>();
        // Now build svpamoves and svpa
        EqualityAlgebra<FiniteSetPred, RoaringBitmap> theory = new EqualityAlgebra<>(unaryTheory);
        UnaryPredicate<FiniteSetPred, RoaringBitmap> trueRet = new UnaryPredicate<>(
                unaryTheory.True(),
                true
        );
        for(Frag f : edges) {
            assert(f.source.type != RefType.ByIdStart);
            assert(f.target.type != RefType.ByIdStart);
            assert(f.source.type != RefType.ByIdEnd);
            assert(f.target.type != RefType.ByIdEnd);
            assert(f.source.type != RefType.SpecificCall);
            assert(f.target.type != RefType.SpecificReturn);
            if(f.target.type == RefType.SpecificCall) {
                moves.add(new Call<>(
                        f.source.specific,
                        f.target.specific,
                        f.source.specific,
                        theory.MkAtom(f.symbol)
                ));
            } else if(f.source.type == RefType.SpecificReturn) {
                moves.add(new Return<>(
                        f.source.specific,
                        f.target.specific,
                        f.source.caller,
                        trueRet
                ));
            } else if(f.source.type == RefType.Specific &&
                    f.target.type == RefType.Specific) {
                moves.add(new Internal<>(
                        f.source.specific,
                        f.target.specific,
                        theory.MkAtom(f.symbol)
                ));
            } else {
                throw new IllegalArgumentException("Weird fragment");
            }
            System.out.format("Add move: %d -> %d%n", f.source.specific, f.target.specific);
        }

        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> svpa = SVPA.MkSVPA(
                moves,
                Collections.singletonList(initial),
                Collections.singletonList(terminal),
                theory
        );

        System.out.format("%d, %d%n", moves.size(), stateCount);
        System.out.format(svpa.toString());

        LinkedList<TaggedSymbol<RoaringBitmap>> witness = svpa.getWitness(theory);
        for(TaggedSymbol<RoaringBitmap> ts : witness) {
            System.out.format("%s:%s%n",ts.toString(),productions.get(ts.input.first()).name);
            int fst = ts.input.first();
            if(fst > terminalCount && fst < terminalCount + nonterminalCount) {
                for(ProdID tag : nonterminals.get(productions.get(fst).name).tags) {
                    System.out.print(tag.name+",");
                }
                System.out.println("");
            }
        }

        Reductionist r = new Reductionist(
                universe,
                terminalMask,
                nonterminalMask,
                tagMask,
                productions,
                terminals,
                nonterminals,
                tags,
                unaryTheory,
                theory,
                svpa
        );
        jread.close();
        fread.close();
        return r;
    }

    private static boolean fillEMsClosure(NonTerminal root,
                                          HashMap<String, Boolean> hasTagsStar) {
        //return true if root has any tags or descendants have any tags
        String name = root.getId().name;
        // Correct behavior depends on having no cycles
        if(hasTagsStar.containsKey(name)) {
            return hasTagsStar.get(name);
        }
        boolean anyTags = !(root.tags.isEmpty());

        hasTagsStar.put(name, anyTags);
        for(List<Production> ps : root.rules) {
            for(Production p : ps) {
                if(p instanceof NonTerminal) {
                    anyTags = fillEMsClosure((NonTerminal)p, hasTagsStar) || anyTags;
                }
            }
        }
        hasTagsStar.put(name, anyTags);
        return anyTags;
    }

    public RoaringBitmap universeBV, terminalsBV, nonterminalsBV, tagsBV;
    public List<ProdID> productions;
    public Map<String, Terminal> terminals;
    public Map<String, NonTerminal> nonterminals;
    public Map<String, ProdID> tags;
    public FiniteSetSolver unaryTheory;
    public EqualityAlgebra<FiniteSetPred, RoaringBitmap> theory;
    public SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> svpa;

    protected Reductionist(RoaringBitmap universeBV,
                           RoaringBitmap terminalsBV,
                           RoaringBitmap nonterminalsBV,
                           RoaringBitmap tagsBV,
                           List<ProdID> productions,
                           Map<String, Terminal> terminals,
                           Map<String, NonTerminal> nonterminals,
                           Map<String, ProdID> tags,
                           FiniteSetSolver unaryTheory,
                           EqualityAlgebra<FiniteSetPred, RoaringBitmap> theory,
                           SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> svpa) {
        this.universeBV = universeBV;
        this.terminalsBV = terminalsBV;
        this.nonterminalsBV = nonterminalsBV;
        this.tagsBV = tagsBV;
        this.productions = productions;
        this.terminals = terminals;
        this.nonterminals = nonterminals;
        this.tags = tags;
        this.unaryTheory = unaryTheory;
        this.theory = theory;
        this.svpa = svpa;
    }

    //TODO: Make this and the rest deterministic?
    public SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> tagSetProperty(Collection<String> tagSet)
            throws TimeoutException, AutomataException {
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> prop = SVPA.getFullSVPA(this.theory);
        EqualityPredicate<FiniteSetPred, RoaringBitmap> retPred = new UnaryPredicate<>(unaryTheory.True(), true);
        for(String t : tagSet) {
            int tagID = this.tags.get(t).id;
            RoaringBitmap tagMask = this.tags.get(t).mask;
            RoaringBitmap producingNTsMask = nonterminals.values().stream().
                    filter(nt -> nt.mask.contains(tagID)).
                    map(nt -> nt.id.mask).
                    reduce(new RoaringBitmap(), (bm1, bm2) -> RoaringBitmap.or(bm1,bm2));
            RoaringBitmap mask = RoaringBitmap.or(tagMask, producingNTsMask);
            List<SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>> moves = new ArrayList<>();
            // Two-state SVPA, just care about hitting that tag
            EqualityPredicate<FiniteSetPred, RoaringBitmap> maskAtom = theory.MkAtom(mask), notMaskAtom = theory.MkNot(maskAtom);
            //Spin in initial state until hitting tag
            moves.add(new Internal<>(0, 0, theory.True()));
            moves.add(new Call<>(0, 0, 0, notMaskAtom));
            //Go to terminal state when hitting tag on a call
            moves.add(new Call<>(0, 1, 0, maskAtom));
            moves.add(new Return<>(0, 0, 0, retPred));
            //Spin in terminal state forever
            moves.add(new Internal<>(1, 1, theory.True()));
            moves.add(new Call<>(1, 1, 0, theory.True()));
            moves.add(new Return<>(1, 1, 0, retPred));
            SVPA <EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> tagProp = SVPA.MkSVPA(
                    moves,
                    Collections.singletonList(0),
                    Collections.singletonList(1),
                    theory
            );
            assert(!tagProp.isEmpty);
            prop = prop.intersectionWith(tagProp.determinize(this.theory), this.theory);
        }
        assert(!prop.isEmpty);
        return prop.determinize(theory);
    }

    public SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> tagSetAbsentProperty(Collection<String> tagSet)
            throws TimeoutException, AutomataException {
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> prop = SVPA.getFullSVPA(this.theory);
        EqualityPredicate<FiniteSetPred, RoaringBitmap> retPred = new UnaryPredicate<>(unaryTheory.True(), true);
        for(String t : tagSet) {
            int tagID = this.tags.get(t).id;
            RoaringBitmap tagMask = this.tags.get(t).mask;
            RoaringBitmap producingNTsMask = nonterminals.values().stream().
                    filter(nt -> nt.mask.contains(tagID)).
                    map(nt -> nt.id.mask).
                    reduce(new RoaringBitmap(), (bm1, bm2) -> RoaringBitmap.or(bm1,bm2));
            RoaringBitmap mask = RoaringBitmap.or(tagMask, producingNTsMask);
            List<SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>> moves = new ArrayList<>();
            // Two-state SVPA, just care about hitting that tag
            // Spin in initial state until hitting tag
            EqualityPredicate<FiniteSetPred, RoaringBitmap> maskAtom = theory.MkAtom(mask), notMaskAtom = theory.MkNot(maskAtom);
            moves.add(new Internal<>(0, 0, theory.True()));
            moves.add(new Call<>(0, 0, 0, notMaskAtom));
            moves.add(new Return<>(0, 0, 0, retPred));
            // Go to stuck state when hitting tag on a call
            moves.add(new Call<>(0, 1, 0, maskAtom));
            // Spin in stuck state forever
            moves.add(new Internal<>(1, 1, theory.True()));
            moves.add(new Call<>(1, 1, 0, theory.True()));
            moves.add(new Return<>(1, 1, 0, retPred));
            SVPA <EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> tagProp = SVPA.MkSVPA(
                    moves,
                    Collections.singletonList(0),
                    Collections.singletonList(0),
                    theory
            );
            assert(!tagProp.isEmpty);
            prop = prop.intersectionWith(tagProp.determinize(this.theory), this.theory);
        }
        assert(!prop.isEmpty);
        return prop.determinize(theory);
    }

    public SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> tagSeqProperty(List<String> tagSet)
            throws TimeoutException, AutomataException {
        EqualityPredicate<FiniteSetPred, RoaringBitmap> retPred = new UnaryPredicate<>(unaryTheory.True(), true);
        List<SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>> moves = new ArrayList<>();
        int stateCount = 0;
        int startState = stateCount++;
        int here = startState;
        // K+1-state SVPA, move from K to K+1 when hitting the right tag.
        //
        for(String t : tagSet) {
            int tagID = this.tags.get(t).id;
            RoaringBitmap tagMask = this.tags.get(t).mask;
            RoaringBitmap producingNTsMask = nonterminals.values().stream().
                    filter(nt -> nt.mask.contains(tagID)).
                    map(nt -> nt.id.mask).
                    reduce(new RoaringBitmap(), (bm1, bm2) -> RoaringBitmap.or(bm1,bm2));
            RoaringBitmap mask = RoaringBitmap.or(tagMask, producingNTsMask);
            int there = stateCount++;
            // Always use 0 stack state because we don't care about the grammar's stack here.
            EqualityPredicate<FiniteSetPred, RoaringBitmap> maskAtom = theory.MkAtom(mask), notMaskAtom = theory.MkNot(maskAtom);
            moves.add(new Internal<>(here, here, theory.True()));
            moves.add(new Call<>(here, here, 0, notMaskAtom));
            moves.add(new Return<>(here, here, 0, retPred));
            //Go to next state when hitting tag on a call
            moves.add(new Call<>(here, there, 0, maskAtom));
            here = there;
        }
        //Spin in terminal state forever
        moves.add(new Internal<>(here, here, theory.True()));
        moves.add(new Call<>(here, here, 0, theory.True()));
        moves.add(new Return<>(here, here, 0, retPred));
        //Build SVPA
        SVPA <EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> tagProp = SVPA.MkSVPA(
                moves,
                Collections.singletonList(startState),
                Collections.singletonList(here),
                theory
        );
        assert(!tagProp.isEmpty);
        return tagProp.determinize(theory);
    }

    public List<TaggedSymbol<RoaringBitmap>> witnessForProperty(SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> prop) throws TimeoutException, AutomataException {
        if(prop == null) {
            return this.svpa.getWitness(this.theory);
        }
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> isec = this.svpa.intersectionWith(prop, this.theory);
        return isec.getWitness(this.theory);
    }
    // TODO: gatherWitnessesForProperty(prop, collector-fn) or witnessIteratorForProperty(prop) or something. Using stream.generate and providing a witness supplier?

    public void printWitness(List<TaggedSymbol<RoaringBitmap>> witness) {
        for(TaggedSymbol<RoaringBitmap> ts : witness) {
            int fst = ts.input.first();
            if(fst <= this.terminals.size()) {
                System.out.format("T %s:%s%n",ts.toString(),productions.get(ts.input.first()).name);
            } else if(fst >= this.terminals.size() && fst < this.terminals.size() + this.nonterminals.size()) {
                System.out.format("NT %s:%s%nTags:",ts.toString(),productions.get(ts.input.first()).name);
                for(ProdID tag : nonterminals.get(productions.get(fst).name).tags) {
                    System.out.print(tag.id+":");
                    System.out.print(tag.name+",");
                }
                System.out.println("");
            } else {
                System.out.format("Other %s:%s%n",ts.toString(),productions.get(ts.input.first()).name);
            }
        }
    }

    public BigInteger getCardinality(int prodLimit)
            throws TimeoutException, AutomataException {
        return this.getCardinality(this.svpa, prodLimit);
    }

    protected class StackState {
        ArrayList<Integer> states;
        StackState() {
            this.states = new ArrayList<>();
        }
        StackState push(int s) {
            StackState s2 = new StackState();
            s2.states = new ArrayList<>(this.states);
            s2.states.add(s);
            assert(s2.states.size() != states.size());
            return s2;
        }
        StackState pop() {
            StackState s2 = new StackState();
            s2.states = new ArrayList<>(this.states);
            s2.states.remove(s2.states.size()-1);
            assert(s2.states.size() != states.size());
            return s2;
        }
        Integer getTop() {
            return this.states.get(this.states.size()-1);
        }
        int size() {
            return this.states.size();
        }
        public int hashCode() {
            return this.states.hashCode();
        }
        public boolean equals(Object o) {
            return o instanceof StackState &&
                    ((StackState)(o)).states.equals(this.states);
        }
    }

    public BigInteger getCardinality(SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> aut, int prodLimit)
            throws TimeoutException, AutomataException {
        aut = SVPA.determinize(aut, this.theory);
        System.out.println("DETERMINIZED");
        BigInteger allFound = BigInteger.ZERO;
        HashMap<Integer, HashMap<StackState, BigInteger>> cardsA = new HashMap<>();
        HashMap<Integer, HashMap<StackState, BigInteger>> cardsB = new HashMap<>();
        HashMap<Integer, HashMap<StackState, BigInteger>> cardsSwap = null;
        for(Integer i : svpa.getInitialStates()) {
            HashMap<StackState, BigInteger> records = new HashMap<>();
            records.put(new StackState(), BigInteger.ONE);
            cardsB.put(i, records);
        }
        HashMap<Integer, Collection<SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>>> movesTo = new HashMap<>();
        HashMap<SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>, Integer> witnessesBy = new HashMap<>();
        for(Integer i : svpa.getStates()) {
            movesTo.put(i, svpa.getMovesTo(i));
            for(SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> move : movesTo.get(i)) {
                witnessesBy.put(move, move.countWitnesses(this.theory));
            }
        }
        for(int k = 1; k < prodLimit; k++) {
            //System.out.println("k: "+k);
            for(Integer i : svpa.getStates()) {
                boolean isFinal = svpa.isFinalState(i);
                HashMap<StackState, BigInteger> toHere = new HashMap<>();
                for(SVPAMove<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> move : movesTo.get(i)) {
                    Integer p = move.from;
                    HashMap<StackState, BigInteger> toThere = cardsB.getOrDefault(p, null);
                    if(toThere == null) {
                        continue;
                    }
                    for(Map.Entry<StackState, BigInteger> toThereS : toThere.entrySet()) {
                        if(toThereS.getValue().equals(BigInteger.ZERO)) {
                            continue;
                        }
                        BigInteger val = toThereS.getValue();
                        int witnesses = witnessesBy.get(move);
                        assert(witnesses >= 0);
                        StackState s = toThereS.getKey();
                       // System.out.println(""+p+"("+s.states+")->"+i+":"+val);
                        if(move instanceof Call) {
                            //push
                            s = s.push(((Call<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>)move).stackState);
                            //System.out.println("Push "+s.states.get(s.states.size()-1));
                        } else if(move instanceof Return) {
                            //pop
                            if(!s.getTop().equals(((Return<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap>)move).stackState)) {
                                //To get from toThereS to here the top of stack s must be the same as the return from there to here
                               // System.out.println("Skip pop "+s.states+":"+move);
                                continue;
                            }
                           // System.out.println("Pop "+s.states.get(s.states.size()-1));
                            s = s.pop();
                        } else if(move instanceof Internal) {
                            //nothing
                            //s = s;
                        } else {
                           // System.out.println(move);
                            assert(false);
                        }
                        BigInteger toHereS = toHere.getOrDefault(s, BigInteger.ZERO);
                        if(witnesses > 1) {
                            //System.out.println("Surprise witness count "+witnesses);
                            assert(false);
                        }
                        BigInteger thisOne = val.multiply(BigInteger.valueOf(witnesses));
                        //System.out.println("Found "+thisOne+" Final? "+isFinal);
                        if (isFinal && s.size() == 0) {
                           // System.out.println(""+thisOne+" paths to "+i+" via "+p);
                            allFound = allFound.add(thisOne);
                        }
                        if(isFinal && s.size() != 0) {
                            //System.out.println("Uh oh");
                            assert(false);
                        }
                        toHere.put(s, toHereS.add(thisOne));
                    }
                }
                cardsA.put(i, toHere);
            }
            cardsSwap = cardsA;
            cardsA = cardsB;
            cardsB = cardsSwap;
            //TODO: use a generation marker instead
            cardsA.clear();
        }
        return allFound;
    }
}
