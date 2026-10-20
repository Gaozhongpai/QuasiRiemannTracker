/- Literal history code for the actual continuing carrier used by
NativeForestAttach. Residual choices remain attached metadata. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowHistoryCode
import Candidate.Research.RecursiveAffine.AttachedFamilyHistory
import Candidate.Research.RecursiveAffine.PhysicalHistoryCode
import Candidate.Cycle63.Moment.DepthTwoCount
import Candidate.Research.RecursiveAffine.HistoryPrepend
import Candidate.Research.RecursiveAffine.NativeForestAttach
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle153SourceReturn
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization CenteredMomentEnergyState
open CenteredMomentSecondHeightFamily

variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
variable (Z Mrow amp xi reserve b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
variable (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

local notation "Rows" => ↥(mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp xi reserve b
  firstHeight N hZ key hz1 hz2 firstIndex)
local notation "first" => fun l=>geometryFirstLabel s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val

/-- Attach chronological provenance on the SAME literal physical
carrier and raw edges as `attach_native_low_rows`. Source facts concern
the selected actual rows; all child histories come from strictly smaller
depth. No independent carrier, prefix count or free residual key is input. -/
def nativeLowAttachedFamilyHistory
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    {eta : Character} {Bnorm T qOwn : ℝ} {root : O}
    (second : Bool) (eps : ℝ)
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root)
    (w : alpha→ℝ) (deleted : Rows→Finset alpha) (q : ℝ) (fees : Rows→ℝ)
    (children : (r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T
      (Cycle63Moment.childMultiplier (!reflected) root units
        (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1))
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (childUnits : Rows→(∀k,History k→FirstSourceLabel→O))
    (childLefts : ℕ→Bool) (Bsrc : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>root) (!reflected) (fun _=>units)
      Z Bsrc (boxes 0) ((),nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r))
    (n : Depth→ℕ)
    (histories : ∀r,LiteralFamilyHistory (children r) n (childUnits r) childLefts Bsrc (fun k=>boxes (k+1))) :=
  attachLiteralFamilyHistory own 1 zero_le_one
    (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex)
    (nativeLowHistoryCode_injective reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex hfirst)
    units childUnits (fun k=>match k with | 0=>!reflected | k+1=>childLefts k) Bsrc boxes sourceFacts
    (fun r=>Cycle63Moment.childMultiplier (!reflected) root units
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1)
    (by
      intro r
      exact old_multiplier_dvd_append (fun _ : Unit=>root) (!reflected) (fun _=>units)
        ((),(nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1))
    (fun _=>rfl) children
    (fun r=>Z^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1.2.1.1
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1.2.1.2
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1.2.2
      Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r))
    (fun _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    (by
      intro r
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (firstSourceMissing_ne_zero (!reflected) (first r.val.1))))
    n histories

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.nativeLowAttachedFamilyHistory
