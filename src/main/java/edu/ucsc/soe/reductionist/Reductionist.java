package edu.ucsc.soe.reductionist;

import automata.AutomataException;
import automata.svpa.*;
import org.roaringbitmap.RoaringBitmap;
import org.sat4j.specs.TimeoutException;
import theory.svpa.equalityalgebra.EqualityAlgebra;
import theory.svpa.equalityalgebra.EqualityPredicate;
import theory.svpa.equalityalgebra.UnaryPredicate;
import utilities.IntegerPair;

import javax.json.*;
import java.io.FileReader;
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

    public static Reductionist fromJSONFile(String path)
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
        RoaringBitmap nonterminalReturnMask = new RoaringBitmap();
        nonterminalReturnMask.add(
                terminalCount+nonterminalCount+tagCount,
                terminalCount+nonterminalCount+tagCount+nonterminalCount
        );

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
        //Stream<ProdID> nonterminalReturnIDs = Arrays.stream(sortedNonTerminalReturns);
        Stream<ProdID> nonterminalReturnIDs = Arrays.stream(new ProdID[0]);
        List<ProdID> productions = Stream.concat(
                Stream.concat(
                        Stream.concat(terminalIDs, nonterminalIDs),
                        tagIDs
                ),
                nonterminalReturnIDs
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
                    } else {
                        steps.add(terminals.get(s));
                    }
                }
                nt.rules.add(steps);
            }
            if(!usedNTs.contains(nt.id.name)) {
                ArrayList<Production> singleStep = new ArrayList<>();
                singleStep.add(nt);
                // TODO: ignoring app_rate
                root.rules.add(singleStep);
            }
        }
        System.out.format("Ts:%d, NTs:%d, tags:%d%n", terminalCount, nonterminalCount, tagCount);
        System.out.format("RN:%s, %d, %d%n", root.id.name, root.id.id, root.rules.size());

        FiniteSetSolver unaryTheory = new FiniteSetSolver(
                terminalCount + nonterminalCount + tagCount
        );

        // Now build frags for each nonterminal
        int stateCount = 0;
        Map<Integer, Integer> ntStarts = new HashMap<>();
        Map<Integer, Integer> ntEnds = new HashMap<>();
        List<Frag> openEdges = new ArrayList<>();
        List<Frag> edges = new ArrayList<>();
        for(NonTerminal nt : sortedNonTerminals) {
            // Allocate start and end states, tie to this NT ID
            int startState = stateCount++;
            int endState = stateCount++;
            ntStarts.put(nt.id.id, startState);
            ntEnds.put(nt.id.id, endState);
            // Create frags for all edges of all productions, including call edges
            for(List<Production> steps : nt.rules) {
                int here = startState;
                Frag active = null;
                for(Production prod : steps) {
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
            //Spin in initial state until hitting tag
            moves.add(new Internal<>(0, 0, theory.True()));
            moves.add(new Call<>(0, 0, 0, theory.True()));
            //Go to terminal state when hitting tag on a call
            moves.add(new Call<>(0, 1, 0, theory.MkAtom(mask)));
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
            prop = prop.intersectionWith(tagProp, this.theory);
        }
        assert(!prop.isEmpty);
        return prop;
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
            moves.add(new Internal<>(0, 0, theory.True()));
            moves.add(new Call<>(0, 0, 0, theory.True()));
            // Go to stuck state when hitting tag on a call
            moves.add(new Call<>(0, 1, 0, theory.MkAtom(mask)));
            moves.add(new Return<>(0, 0, 0, retPred));
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
            prop = prop.intersectionWith(tagProp, this.theory);
        }
        assert(!prop.isEmpty);
        return prop;
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
            moves.add(new Internal<>(here, here, theory.True()));
            moves.add(new Call<>(here, here, 0, theory.True()));
            moves.add(new Return<>(here, here, 0, retPred));
            //Go to next state when hitting tag on a call
            moves.add(new Call<>(here, there, 0, theory.MkAtom(mask)));
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
        return tagProp;
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

    public Integer getCardinality(int prodLimit)
            throws TimeoutException, AutomataException {
        return this.getCardinality(this.svpa, prodLimit);
    }
    public Integer getCardinality(SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> aut, int prodLimit)
            throws TimeoutException, AutomataException {
        aut = SVPA.determinize(aut, this.theory);
        System.out.println("DETERMINIZED");
        // Use the Chomsky reachability recursion via dynamic programming
        HashMap<IntegerPair, Integer> cards = new HashMap<>();
        for(int k = 0; k < prodLimit; k++) {
            for(Integer i : svpa.getStates()) {
                //...
            }
        }
        // Note: the sum isn't just over (state,letter) but over (state, stack_state) , and we use a hypothetical
        //  getWitnessCount() to figure out how many "letters" could get us from state,stack_state into this_state and add that many.
        //  That way we don't actually enumerate over every witness, but have a nice closed form solution.
        return 0;
    }
}
