package edu.ucsc.soe.reductionist;

import java.util.Objects;
import org.roaringbitmap.RoaringBitmap;

public class FiniteSetPred {
    public final RoaringBitmap bv;
    // TODO: optimize for case where value = n = just one
    // OR = or if both bvs, add or make new bv if both ints
    // AND = and if both bvs, contains or empty if both ints and not equal
    // NOT = bv.not or universe - me
    // EQUALS = bv equality if both bvs; bv AND me = me, bv OR me = bv; OR equal if both ints
    public FiniteSetPred(int n) {
        this(RoaringBitmap.bitmapOf(n));
    }
    public FiniteSetPred(RoaringBitmap b) {
        this.bv = b;
    }
    public boolean isSatisfiedBy(RoaringBitmap bm) {
        return RoaringBitmap.andCardinality(this.bv, bm) > 0;
    }
    @Override
    public String toString() {
        return "Set:" + this.bv.toString();
    }
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof FiniteSetPred) {
            return Objects.equals(this.bv, ((FiniteSetPred) obj).bv);
        }
        return false;
    }
    @Override
    public int hashCode() {
        return Objects.hash(FiniteSetPred.class, bv);
    }
}
