/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeContinuationSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentAllocatedRayDictionary CenteredMomentCanonicalFirst
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy CenteredMomentEligibleEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyPaidBands
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentAllocatedChildCapacity CenteredMomentAllocatedNaturalSource
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
variable {α : Type*} [Fintype α]
local instance continuationStepDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A genuine regional LOW step constructs the next actual affine input.
The right side is its literal native energy at base Z^unit and width1.
The attaining deleted subset and inherited original ray dictionary are
constructed from the native LOW detector; no continuation energy estimate,
returned record, desired model length, or recursive callback is assumed.
The equal-product comparison is chosen by the actual next regional ledger.
Its admissible regional window is proved separately from source geometry. -/
theorem actual_low_continuation_input
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ Cpay : ℝ, 1 ≤ Cpay ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (hZ : 1 < Z) (s : Input α) (θ : α → RayQuotient.Characters M H)
        (w σ freq : α → ℝ) (t height mesh a del : ℝ) (i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z →
      (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j, w j ≤ mesh) →
      ∀ (hσlo : ∀ j, σmin ≤ σ j) (hσhi : ∀ j, σ j ≤ σmax),
      0 ≤ height → (∀ j, |freq j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 → 0 ≤ del →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ (ch : Chain s) (χ : Character) (Q : Ideal O) (hP : ch.R₂*ch.E₂ ≠ 0)
        (hPN : ((ch.R₂*ch.E₂).absNorm : ℝ) ≤ Z^Bmask) (radius : ℝ)
        (C D : Ideal O) (U : Finset (CommonIndex C D)) (second : Bool) (L : Ideal O)
        (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2))),
      let st := retainedState Z Bmask hZ χ Q (ch.R₂*ch.E₂) hP hPN radius C D U
      let src := ch.final χ t
      let J := ch.indices L alloc
      st.width ≤ Mcap →
      ∀ (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus),
      let low := ActualLow M H hH st η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∀ (unit : ℝ) (hunit : 0 < unit) (hwide : st.width ≤ unit)
        (hmask : (st.puncture.absNorm : ℝ) ≤ (Z ^ unit) ^ (20 : ℝ))
        (p : Profiles (1/4) (9/4)), s.W₁ = (p.profile 0 : ℝ → ℂ) →
      s.W₂ = (p.profile 1 : ℝ → ℂ) →
      ∀ (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂),
      ∀ hprod : Y₁ * Y₂ = rawDaughterScale src second L alloc 0 * rawDaughterScale src second L alloc 1,
      ∃ (R : Finset α) (_hR : R ⊆ J), (∑ j ∈ R, w j) ≤ del+mesh ∧
        (R = J ∨ del ≤ ∑ j ∈ R, w j) ∧
        let nextState := nativeContinuationState st unit hunit hwide hmask
        let nextInput := nativeContinuationInput M H hH η₀ (fun j : ↥(J \ R) => θ j)
          W hW.continuous A B σmin σmax hA hWs (fun j => w j) (fun j => σ j) (fun j => freq j)
          (fun j => ⟨hσlo j, hσhi j⟩) st unit hunit hwide hmask p (by norm_num)
          t (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1) Y₁ Y₂
          (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
          hY₁ hY₂ hprod
        finalPositiveEnergy src second L alloc (fun z => st.radial.keep z ∧ low z)
          st.radial.profile st.radial.scale ≤
        Cpay^(Fintype.card α)*Z^(2*ε*d*(Fintype.card α : ℝ)+q*(del+mesh)) *
          energy nextInput.η nextState.mask 1 nextInput.t nextInput.W₁ nextInput.W₂
            nextInput.slots nextInput.coefficient nextInput.P nextInput.X₁ nextInput.X₂
            nextState.radial.keep nextState.radial.profile nextState.radial.scale := by
  obtain ⟨Cpay, hCpay, hsource⟩ := actual_regional_daughter_source (α:=α) M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax Mcap Bmask margin d hRw hdmax hτ hε he he' hκ hη
    hbudget hmargin hd hdsupply hdm q hq₀ hq₁
  refine ⟨Cpay, hCpay, ?_⟩
  intro η₀
  filter_upwards [hsource η₀] with Z hz
  refine ⟨hz.1, ?_⟩
  intro hZ s θ w σ freq t height mesh a del i hmatch hw hwr hmesh hwm hσlo hσhi hheight hfreq ha ha'
    hdel hfreqbin hhigh ch χ Q hP hPN radius C D U second L alloc st src J hwidth hQM hQη low
    unit hunit hwide hmask p hp₁ hp₂ Y₁ Y₂ hY₁ hY₂ hprod
  obtain ⟨R, hR, hsum, hcover, hbound⟩ := hz.2 hZ s θ w σ freq t height mesh a del i hmatch hw hwr
    hmesh hwm hσlo hσhi hheight hfreq ha ha' hdel hfreqbin hhigh ch χ Q hP hPN radius C D U
    second L alloc hwidth hQM hQη
  refine ⟨R, hR, hsum, hcover, ?_⟩
  dsimp only
  have hnext := nativeContinuationInput_energy M H hH η₀ (fun j : ↥(J \ R) => θ j)
    W hW.continuous A B σmin σmax hA hWs (fun j => w j) (fun j => σ j) (fun j => freq j)
    (fun j => ⟨hσlo j, hσhi j⟩) st unit hunit hwide hmask p (by norm_num)
    t (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1) Y₁ Y₂
    (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
    hY₁ hY₂ hprod
  dsimp only at hnext
  erw [hnext]
  rw [← hp₁, ← hp₂]
  exact hbound

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_low_continuation_input
