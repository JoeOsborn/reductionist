package edu.ucsc.soe.reductionist;

import automata.svpa.SVPA;
import automata.svpa.SVPAMove;
//import sometheory 
import org.roaringbitmap.RoaringBitmap;

import java.util.*;

import java.io.FileReader;
import javax.json.*;

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
            this.tags = new ArrayList<ProdID>();
            this.rules = new ArrayList<List<Production>>();
        }
    }
    protected static class Terminal extends Production {
        public Terminal(String n) {
            super(n);
        }
    }

    public static Reductionist fromJSONFile(String path)
        throws java.io.FileNotFoundException, java.io.IOException {
        FileReader fread = new FileReader(path);
        JsonReader jread = Json.createReader(fread);
        JsonObject jobj = jread.readObject();

        JsonObject nts = jobj.getJsonObject("nonterminals");

        HashMap<String, NonTerminal> nonterminals = new HashMap<String, NonTerminal>();
        NonTerminal root = new NonTerminal(" root");
        nonterminals.put(root.id.name, root);
        HashMap<String, Terminal> terminals = new HashMap<String, Terminal>();
        HashMap<String, ProdID> tags = new HashMap<String, ProdID>();

        // Find every nonterminal, terminal, and tag.
        // Also note which nonterminals are used.
        HashSet<String> usedNTs = new HashSet<String>();
        for(Map.Entry<String, JsonValue> entry : nts.entrySet()) {
            JsonObject prodObj = (JsonObject)entry.getValue();
            NonTerminal nt = new NonTerminal(entry.getKey());
            nonterminals.put(nt.id.name, nt);
            JsonValue markup = prodObj.get("markup");
            if(markup != JsonValue.NULL) {
                for(Map.Entry<String, JsonValue> markupTags : ((JsonObject)markup).entrySet()) {
                    for(JsonValue tagValue : (JsonArray)markupTags.getValue()) {
                        String tag = markupTags.getKey() + "#:#" + ((JsonString)tagValue).getString();
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
        int terminalCount = terminals.size();
        int nonterminalCount = nonterminals.size();
        int tagCount = tags.size();
        RoaringBitmap universe = new RoaringBitmap();
        universe.add(0, terminalCount + nonterminalCount + tagCount);
        RoaringBitmap terminalMask = new RoaringBitmap();
        terminalMask.add(0, terminalCount);
        RoaringBitmap nonterminalMask = new RoaringBitmap();
        nonterminalMask.add(terminalCount, terminalCount + nonterminalCount);
        RoaringBitmap tagMask = new RoaringBitmap();
        tagMask.add(terminalCount+nonterminalCount, terminalCount+nonterminalCount+tagCount);

        // Number every terminal, nonterminal, and tag!

        Terminal[] sortedTerminals = terminals.keySet().stream().
            sorted().map(str -> terminals.get(str)).toArray(Terminal[]::new);
        NonTerminal[] sortedNonTerminals = nonterminals.keySet().stream().
            sorted().map(str -> nonterminals.get(str)).toArray(NonTerminal[]::new);
        ProdID[] sortedTags = tags.keySet().stream().
            sorted().map(str -> tags.get(str)).toArray(ProdID[]::new);
        for(int i = 0; i < sortedTerminals.length; i++) {
            sortedTerminals[i].id.id = i;
            sortedTerminals[i].id.mask = RoaringBitmap.bitmapOf(i);
        }
        for(int i = 0; i < sortedTags.length; i++) {
            int id = i + terminalCount + nonterminalCount;
            sortedTags[i].id = id;
            // TODO: could also store the "type" of the markup in this mask?
            sortedTags[i].mask = RoaringBitmap.bitmapOf(id);
        }
        for(int i = 0; i < sortedNonTerminals.length; i++) {
            NonTerminal nt = sortedNonTerminals[i];
            int id = i + terminalCount;
            //System.out.println(nt.id.name+":"+id);
            nt.id.id = id;
            nt.id.mask = RoaringBitmap.bitmapOf(id);
            nt.mask = RoaringBitmap.bitmapOf(id);
            for(ProdID tag : nt.tags) {
                nt.mask.or(tag.mask);
            }
        }

        // Now hook up references and add any un-referenced rules to the root nonterminal.

        for(Map.Entry<String, JsonValue> entry : nts.entrySet()) {
            JsonObject prodObj = (JsonObject)entry.getValue();
            NonTerminal nt = nonterminals.get(entry.getKey());
            for(JsonValue ruleVal : prodObj.getJsonArray("rules")) {
                JsonObject rule = (JsonObject)ruleVal;
                // TODO: ignoring app_rate
                ArrayList<Production> steps = new ArrayList<Production>();
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
                ArrayList<Production> singleStep = new ArrayList<Production>();
                singleStep.add(nt);
                // TODO: ignoring app_rate
                root.rules.add(singleStep);
            }
        }
        System.out.format("Ts:%d, NTs:%d, tags:%d%n", terminalCount, nonterminalCount, tagCount);
        System.out.format("RN:%s, %d, %d%n", root.id.name, root.id.id, root.rules.size());

        // Now build frags for each nonterminal

        // Now connect up frags along start/end

        // Now build svpamoves and svpa

        // Now return the svpa or a reductionist wrapping it and give it functions for doing the right thing with properties?
        
        Reductionist r = new Reductionist();
        jread.close();
        fread.close();
        return r;
    }
    protected Reductionist() {

    }
}
