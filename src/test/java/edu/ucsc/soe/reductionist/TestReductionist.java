package edu.ucsc.soe.reductionist;

import org.junit.Test;

import static org.junit.Assert.assertTrue;

public class TestReductionist {
    @Test
    public void CreateSVPA () throws Exception {
        Reductionist r = Reductionist.fromJSONFile("talktown/talktown-aiide-study-2016.json");
        assertTrue(true);
        // TODO: create a property and test it!!!
        
    }
}
