package edu.ucsc.soe.reductionist;

import automata.svpa.*;
import org.roaringbitmap.RoaringBitmap;
import theory.svpa.equalityalgebra.EqualityAlgebra;
import theory.svpa.equalityalgebra.EqualityPredicate;
import theory.svpa.equalityalgebra.UnaryPredicate;

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
            for(JsonValue ruleVal : prodObj.getJsonArray("rules")) {
                JsonObject rule = (JsonObject)ruleVal;
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
            for(JsonValue ruleVal : prodObj.getJsonArray("rules")) {
                JsonObject rule = (JsonObject)ruleVal;
                // TODO: ignoring app_rate
                ArrayList<Production> steps = new ArrayList<>();
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
        this.theory = theory;
        this.svpa = svpa;
    }
}
