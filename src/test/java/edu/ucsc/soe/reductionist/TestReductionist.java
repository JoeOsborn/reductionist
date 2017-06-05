package edu.ucsc.soe.reductionist;

import org.junit.Test;

public class TestReductionist {
    @Test
    public void CreateSVPA () throws Exception {
        Reductionist r = Reductionist.fromJSONFile("talktown/talktown-aiide-study-2016.json", false);
        //todo: fix counting. fae one should have 417 EMs??  unless those are also double counted...
        // ah! It could be that there are 102 distinct meaning-producing paths, some of which have multiple tags, so the EM counting might have different subsets of those showing up... like if "A" and "B" always occur together the result of james's thing will be 3*|ab|/.  also this thing counts orderings of tags and not sets of tags.
        //Reductionist r = Reductionist.fromJSONFile("talktown/talktown-aiide-study-2016.json", false);
        System.out.format("Card: %d%n", r.getCardinality(50));

//        System.out.println("A trace where we say our first and last name");
//        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> firstlast = r.tagSetProperty(Arrays.asList("Moves#:#say first name", "Moves#:#say last name"));
//        System.out.println("Try now");
//        List<TaggedSymbol<RoaringBitmap>> witness = r.witnessForProperty(firstlast);
//        r.printWitness(witness);
//        System.out.println("A trace where we don't say our first or last name or storm off");
//        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> notfirst = r.tagSetAbsentProperty(Arrays.asList("Moves#:#say first name", "Moves#:#say last name", "Moves#:#storm off"));
//        System.out.println("Try now");
//        witness = r.witnessForProperty(notfirst);
//        r.printWitness(witness);
//        System.out.println("A trace where we say last name then first name");
//        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> lastThenFirst = r.tagSeqProperty(Arrays.asList("Moves#:#say last name", "Moves#:#say first name"));
//        System.out.println("Try now");
//        witness = r.witnessForProperty(lastThenFirst);
//        r.printWitness(witness);
//        System.out.println("Cardinality of that one for strings up to length 100 productions:");
//        SVPA<EqualityPredicate<FiniteSetPred,RoaringBitmap>, RoaringBitmap> svpa = r.svpa.intersectionWith(lastThenFirst, r.theory);
//        System.out.println(r.getCardinality(svpa, 100));
//        System.out.println("VS whole grammar:");
//        System.out.println(r.getCardinality(100));
    }
}
