package edu.ucsc.soe.reductionist;

import static org.junit.Assert.assertEquals;
import org.junit.Test;

import org.roaringbitmap.RoaringBitmap;

import edu.ucsc.soe.reductionist.Reductionist;
import edu.ucsc.soe.reductionist.FiniteSetPred;
import edu.ucsc.soe.reductionist.FiniteSetSolver;

public class TestFiniteSet {
    @Test
    public void BVBehavior () {
        RoaringBitmap big = new RoaringBitmap();
        big.add(5, 100L);
        RoaringBitmap small = RoaringBitmap.bitmapOf(5);
        assertEquals(RoaringBitmap.or(small,big),(big));
        assertEquals(RoaringBitmap.and(small,big),small);
        RoaringBitmap zero = new RoaringBitmap();
        RoaringBitmap one = RoaringBitmap.bitmapOf(1);
        assertEquals(RoaringBitmap.xor(RoaringBitmap.or(big, one), big),one);
        one.and(big);
        assertEquals(one, zero);
    }
}
