package edu.ucsc.soe.reductionist;

import static org.junit.Assert.*;
import org.junit.Test;

import org.roaringbitmap.RoaringBitmap;

import edu.ucsc.soe.reductionist.Reductionist;
import edu.ucsc.soe.reductionist.FiniteSetPred;
import edu.ucsc.soe.reductionist.FiniteSetSolver;

import automata.svpa.*;

public class TestReductionist {
    @Test
    public void CreateSVPA () throws Exception {
        Reductionist r = Reductionist.fromJSONFile("talktown/TeacherTexts.json");
        assertTrue(true);
    }
}
