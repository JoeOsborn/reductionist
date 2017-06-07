package edu.ucsc.soe.reductionist;

import org.junit.Test;

import java.math.BigInteger;

public class TestReductionist {
    @Test
    public void CreateSVPA () throws Exception {
        Reductionist r2 = Reductionist.fromJSONFile("expressionist/grammars/load/tenderclaws.json", false);
        BigInteger card2 = r2.getCardinality(33);
        System.out.println("Card:"+card2);
        assert(card2.equals(BigInteger.valueOf(108)));

        Reductionist r = Reductionist.fromJSONFile("faeMemoryLibrary.json", false);
        BigInteger card = r.getCardinality(60);
        System.out.println("Card:"+card);
        assert(card.equals(BigInteger.valueOf(159)));

        //Reductionist r = Reductionist.fromJSONFile("faeMemoryLibrary.json", false);
        //Reductionist r = Reductionist.fromJSONFile("joeTest.json", false);
        //todo: fix counting. fae one should have 417 EMs??  unless those are also double counted...
        // ah! It could be that there are 102 distinct meaning-producing paths, some of which have multiple tags, so the EM counting might have different subsets of those showing up... like if "A" and "B" always occur together the result of james's thing will be 3*|ab|/.  also this thing counts orderings of tags and not sets of tags.
        //Reductionist r = Reductionist.fromJSONFile("talktown/talktown-aiide-study-2016.json", false);
        // TODO: use diameter of SVPA as limit default
        //System.out.format("Card: %s%n", r.getCardinality(5000).toString());

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
