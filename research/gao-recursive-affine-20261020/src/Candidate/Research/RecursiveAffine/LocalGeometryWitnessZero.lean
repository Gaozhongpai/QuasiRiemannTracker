import Candidate.Research.RecursiveAffine.LocalGeometryWitness
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle153LocalHighWitness
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum Cycle63InitialMass
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable [Cycle63.AffineLedger] in
/-- The actual native bin supplies the zero lower bound of the same physical
state and row retained by the local witness. Only height monotonicity is used. -/
theorem localGeometryWitness_zero_ge {ι α Label : Type}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (η η₀ : Character) (F₀ : NaturalRow η 1)
    (reflected second : Bool) (s : Input ι) (hs : ParentPresentation s.η F₀ 1)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label → SecondInputDatum α) (first : Label → FirstSourceLabel)
    (r : secondLiveRows (fun l => (d l).block))
    (hparent : (d r.val.1).input.η = geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1 = geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R ≠ 0) (ψ : RayCharacter)
    {Zs Bmask bΦ : ℝ} (st : NaturalState Zs Bmask bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (zr : O) (hzr : st.radial.keep zr)
    (hchar : st.character = (d r.val.1).τ ψ)
    (hpuncture : st.puncture = (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
    (hrow : zr = if second then -r.val.2.2.2.val else r.val.2.2.2.val)
    (e T0 Tz : ℝ) (p : BufferIndex e)
    (hzb : GeometryZeroBin M H hH st η₀ hQM hQη zr hzr e T0 p)
    (hT : ((3*p.1.val : ℕ) : ℝ)*T0 ≤ Tz) :
    bufferValue e p ≤ (localGeometryWitness M η η₀ F₀ reflected second s hs R seed K Z ξ hK bin j d first r hparent hfirst hR ψ st hQM hQη zr hzr hchar hpuncture hrow).zeroMax M H hH Tz :=
  hzb.2.2.2.2.1.trans (zeroMaximum_mono _ _ hT)

end
end OAI.SevenEighths.Cycle153LocalHighWitness

#print axioms OAI.SevenEighths.Cycle153LocalHighWitness.localGeometryWitness_zero_ge
