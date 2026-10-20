/- Literal own-HIGH node of the recursive source tree. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualHighNodeProducer
import Candidate.Research.RecursiveAffine.NativeAffineContinuation
import Candidate.Research.RecursiveAffine.ActualFamilyRebase

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RecursiveHighProvider
noncomputable section
open Cycle153HighProvider Cycle153SourceReturn Cycle153RegionalLow
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open Cycle63Moment Cycle63Moment.LowBranch Cycle63InitialMass
open ConcretePrimeRowBridge CompletedGauss Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot

variable {Base : Type} {base : Character → Base → Character}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable [Cycle63.AffineLedger]

/-- At the literal continuing LOW source, produce its actual own HIGH
record and rebase it back to the original global base. The input is the
native regional comparison of the same retained state and original ray
coefficients. Rebase preserves its value and physical classes; all paid
exponents are multiplied by the actual unit. -/
theorem actual_continuation_high_node
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (mesh ε τlow B lossNeeded : ℝ)
    (Ψ : 𝓢(ℝ,ℂ)) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Z U oldMask : ℝ)
    (hZ : 1<Z) (hU : 0<U) (hU1 : U ≤ 1) (hB : 0 ≤ B)
    (hsource : ActualHighNodeAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi
      g (1/4) (9/4) 2 20 mesh ε τlow B lossNeeded (by norm_num) Ψ SH dh Kclass Kh η₀ Q hQM hQ72 (Z^U))
    (hlocalZ : 1<Z^U) (hT : 2<(Z^U)^g.τ) (T : Finset α)
    (θ : T→RayQuotient.Characters M H) (w σ freq : T→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50)) (t height : ℝ)
    (hw : ∀i,0 ≤ w i) (hmesh : ∀i,w i/U ≤ mesh)
    (hheight : 0 ≤ height) (hfreq : ∀i,|freq i| ≤ height)
    (state : NaturalState Z oldMask 2) (hfixed : state.fixedModulus=internalQ Q η₀)
    (hwide : state.width ≤ U) (hmask : (state.puncture.absNorm:ℝ) ≤ (Z^U)^(20:ℝ))
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hwindow : Cycle63.AffineLedger.PlainWindow (length (Z^U) X₁) (length (Z^U) X₂) (∑i,w i/U))
    (P : PrefixHighPresentation (base η₀) state.character state.puncture)
    (τT : ℝ) (hτT : τlow ≤ τT)
    (hvbound : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ (Z^U)^(B-130)) :
    let nextState:=nativeContinuationState state U hU hwide hmask
    let nextInput:=nativeRegionalContinuationInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state U hU hwide hmask p (by norm_num) t X₁ X₂ hX₁ hX₂
    let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i,w i/U)))
    ∃part : ReturnedPartAt M H hH Cycle63.AffineLedger.q
        (fun η=>extendFixedDictionary (base η)) η₀ Z B ((Z^U)^τT) P.mult,
      part.scale=state.rowWidth ∧ part.length=U*Real.logb (Z^U) (volume nextInput) ∧
      part.amp=U*amp ∧ part.loss=U*(lossNeeded+ε) ∧
      (∀b,(Fintype.card (part.record b).Class:ℝ) ≤ Kclass) ∧
      GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi (Z^U) hlocalZ hT (1/4) (9/4)
        nextInput p state.puncture 1 nextState.rowWidth amp Ψ
        (profile_zero_of_pos p (by norm_num) 0) (profile_zero_of_pos p (by norm_num) 1) SH dh height
        (Kh*((Z^U)^(-(nextState.rowWidth+3*g.δ-amp+ε))*part.value+1)) := by
  intro nextState nextInput amp
  have hwidth : nextState.width ≤ 1 := (nativeContinuationState_width state U hU hwide hmask).le
  obtain ⟨localPart,hm,hlen,ha,hl,hcard,hphysical⟩ := hsource hlocalZ hT T θ (fun i=>w i/U) σ freq hσ t height
    (fun i=>div_nonneg (hw i) hU.le) hmesh hheight hfreq nextState hfixed hwidth
    p X₁ X₂ hX₁ hX₂ hwindow P τT hτT hvbound
  let part:=rebaseReturnedPartFixedCap hZ hU hU1 hB localPart
  have hvalue : part.value=localPart.value :=
    rebaseReturnedPartFixedCap_value hZ hU hU1 hB localPart
  refine ⟨part,?_,?_,?_,?_,?_,?_⟩
  · change U*localPart.scale=state.rowWidth
    rw [hm]
    change U*(state.rowWidth/U)=state.rowWidth
    field_simp
  · change U*localPart.length=U*Real.logb (Z^U) (volume nextInput)
    rw [hlen]
    rfl
  · change U*localPart.amp=U*amp
    rw [ha]
  · change U*localPart.loss=U*(lossNeeded+ε)
    rw [hl]
  · exact hcard
  · rw [hvalue]
    exact hphysical

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
#print axioms OAI.SevenEighths.Cycle153RecursiveHighProvider.actual_continuation_high_node
