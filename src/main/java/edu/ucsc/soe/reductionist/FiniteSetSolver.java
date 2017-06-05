package edu.ucsc.soe.reductionist;

import theory.BooleanAlgebra;
import utilities.Pair;

import org.roaringbitmap.RoaringBitmap;
import org.roaringbitmap.FastAggregation;

import java.util.Collection;
import java.util.stream.Stream;

public class FiniteSetSolver extends BooleanAlgebra<FiniteSetPred, RoaringBitmap> {
    RoaringBitmap universe, zero, independentUniverse;
    FiniteSetPred puniverse, pzero;
    long independentDomainSize;
    
    public FiniteSetSolver(long domain_size, long independentDomainSize) {
        universe = new RoaringBitmap();
        universe.add(0L, domain_size);
        puniverse = new FiniteSetPred(universe);
        zero = new RoaringBitmap();
        pzero = new FiniteSetPred(zero);
        this.independentDomainSize = independentDomainSize;
        this.independentUniverse = new RoaringBitmap();
        this.independentUniverse.add(0L, independentDomainSize);
    }
    
    @Override
    public FiniteSetPred MkAtom(RoaringBitmap b) {
        return new FiniteSetPred(b);
    }
    @Override
    public FiniteSetPred MkNot(FiniteSetPred p) {
        // a ^ FFFF = 1 where a is 0, 0 where a is 1 = ~a
        return new FiniteSetPred(RoaringBitmap.xor(p.bv, universe));
    }
    // TODO: Better to put the collection version of OR into FiniteSetPred too?
    @Override
    public FiniteSetPred MkOr(Collection<FiniteSetPred> pset) {
        Stream<RoaringBitmap> bms = pset.stream().map(p -> p.bv);
        return new FiniteSetPred(FastAggregation.or(bms.iterator()));
    }
    @Override
    public FiniteSetPred MkOr(FiniteSetPred a, FiniteSetPred b) {
        return new FiniteSetPred(RoaringBitmap.or(a.bv, b.bv));
    }
    @Override
    public FiniteSetPred MkAnd(Collection<FiniteSetPred> pset) {
        Stream<RoaringBitmap> bms = pset.stream().map(p -> p.bv);
        return new FiniteSetPred(FastAggregation.and(bms.iterator()));
    }
    @Override
    public FiniteSetPred MkAnd(FiniteSetPred a, FiniteSetPred b) {
        return new FiniteSetPred(RoaringBitmap.and(a.bv, b.bv));
    }
    @Override
    public FiniteSetPred True() {
        return puniverse;
    }
    @Override
    public FiniteSetPred False() {
        return pzero;
    }
    @Override
    public boolean AreEquivalent(FiniteSetPred a, FiniteSetPred b) {
        // ?? or else ~ (sat(A & ~B) || sat(~A & B))  
        return a.bv.equals(b.bv);
    }
    @Override
    public boolean IsSatisfiable(FiniteSetPred a) {
        return a.bv.getCardinality() > 0;
    }
    @Override
    public boolean HasModel(FiniteSetPred p, RoaringBitmap el) {
        return p.isSatisfiedBy(el); 
    }
    @Override
    public boolean HasModel(FiniteSetPred p1, RoaringBitmap el1, RoaringBitmap el2) {
        throw new UnsupportedOperationException("Not supported yet.");
    }
    @Override
    public RoaringBitmap generateWitness(FiniteSetPred p) {
        return p.bv;
        // // TODO: something smarter with tags?  Or just return p?  Is the empty set a witness?
        // for(int i : p.bv) {
        //     return RoaringBitmap.bitmapOf(i);
        // }
        // return null;
    }
    @Override
    public Pair<RoaringBitmap, RoaringBitmap> generateWitnesses(FiniteSetPred p1) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public int countWitnesses(FiniteSetPred p) {
        //how many elements of the universe does p contain?
        //here I actually only care about the NTs and Ts, not the tags.
        //FIXME: ? special case the universe which is mainly used for returns?
        if(p.bv.equals(universe)) {
            return 1;
        }
        int interestingPart = RoaringBitmap.andCardinality(p.bv, this.independentUniverse);
        if(interestingPart > 0) {
            return interestingPart;
        }
        //FIXME: ? Is this right?
        return 1;
    }
}
