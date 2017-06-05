package edu.ucsc.soe.reductionist;

import automata.svpa.SVPA;
import automata.svpa.TaggedSymbol;
import org.junit.Test;
import org.roaringbitmap.RoaringBitmap;
import theory.svpa.equalityalgebra.EqualityPredicate;

import java.util.Arrays;
import java.util.List;

public class TestReductionist {
    @Test
    public void CreateSVPA () throws Exception {
        Reductionist r = Reductionist.fromJSONFile("talktown/talktown-aiide-study-2016.json", true);
        //todo: count
        //Reductionist r = Reductionist.fromJSONFile("talktown/talktown-aiide-study-2016.json", false);
        System.out.format("Card: %d%n", r.getCardinality(100));
        System.out.println("A trace where we say our first and last name");
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> firstlast = r.tagSetProperty(Arrays.asList("Moves#:#say first name", "Moves#:#say last name"));
        System.out.println("Try now");
        List<TaggedSymbol<RoaringBitmap>> witness = r.witnessForProperty(firstlast);
        r.printWitness(witness);
        System.out.println("A trace where we don't say our first or last name or storm off");
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> notfirst = r.tagSetAbsentProperty(Arrays.asList("Moves#:#say first name", "Moves#:#say last name", "Moves#:#storm off"));
        System.out.println("Try now");
        witness = r.witnessForProperty(notfirst);
        r.printWitness(witness);
        System.out.println("A trace where we say last name then first name");
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> lastThenFirst = r.tagSeqProperty(Arrays.asList("Moves#:#say last name", "Moves#:#say first name"));
        System.out.println("Try now");
        witness = r.witnessForProperty(lastThenFirst);
        r.printWitness(witness);
        System.out.println("Cardinality of that one for strings up to length 100 productions:");
        SVPA<EqualityPredicate<FiniteSetPred,RoaringBitmap>, RoaringBitmap> svpa = r.svpa.intersectionWith(lastThenFirst, r.theory);
        System.out.println(r.getCardinality(svpa, 100));
        System.out.println("VS whole grammar:");
        System.out.println(r.getCardinality(100));
    }
}
