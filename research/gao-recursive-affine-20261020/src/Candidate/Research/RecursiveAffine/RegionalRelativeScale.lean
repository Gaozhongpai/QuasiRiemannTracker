/- The energy scale of the child of a live final daughter of a LOW child: added to the log norm of the multiplier of its
row, it is at most the second coordinate of the high chain of the first label, up to the constants of the presentation.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildScale

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondRetainedWidth CenteredMomentSecondCanonicalNonunit
open Cycle63Moment Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity Cycle63InitialMass
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual scale identity at an arbitrary global prefix. The parent
multiplier log is retained, instead of assuming it is negligible as in the
original first-prefix caller. This is the scale bridge required by the
strict-depth raw payment recurrence. -/
theorem actual_live_main_row_scale_relative {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hZ : 1 < Z) (hb : 0 < b)
    (reflected left second : Bool) (first : FirstSourceLabel) (reserve ε : ℝ)
    (hfirst₁ : Supported first.1.1) (hfirst₂ : Supported first.1.2)
    (hfirst : primeSupport first.1.1 = primeSupport first.1.2)
    (hradius : g.datum.radius = frequencyRadius
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N first) Z ξ)
    (C₂ D₂ : Ideal O) (U₂ : Finset (CommonIndex C₂ D₂))
    (hC : g.datum.C = C₂) (hD : g.datum.D = D₂) (hU : HEq g.datum.inactive U₂)
    (u₀ : O) (unit : FirstSourceLabel → O) (hunit : ∀ l, IsUnit (unit l))
    (hmult : childMultiplier left u₀ unit ⟨first, (C₂, D₂), U₂⟩ ≠ 0)
    {Bmask : ℝ} (τ : Character) (Q P : Ideal O) (hP : P ≠ 0) (hPN : (P.absNorm : ℝ) ≤ Z^Bmask) :
    (retainedState Z Bmask hZ τ Q P hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive).rowWidth +
        Real.logb Z ((Ideal.span {childMultiplier left u₀ unit ⟨first, (C₂, D₂), U₂⟩}).absNorm : ℝ) ≤ actualHighCoordinates reflected left second first C₂ D₂ U₂ Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε 2 - ε +
        Real.logb Z (normValue u₀) +
        (Real.logb Z 4 + 2*(N : ℝ)*Real.logb Z b + ξ/2) := by
  have hfit := live_frequency_generators_fit (fun _ : Unit => g.datum) g.row
  change normValue (commonFrequencyGenerator g.datum.C g.datum.D) *
    normValue (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive) ≤ 4 * g.datum.radius at hfit
  subst hC hD
  have hU' : g.datum.inactive = U₂ := eq_of_heq hU
  subst hU'
  rw [hradius] at hfit
  have hfun : (fun l => ((hunit l).unit : O)) = unit := funext fun l => (hunit l).unit_spec
  have hid : Real.logb Z (retainedScale (frequencyRadius
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N first) Z ξ)
        g.datum.C g.datum.D g.datum.inactive) +
      Real.logb Z (normValue (childMultiplier left u₀ unit ⟨first, (g.datum.C, g.datum.D), g.datum.inactive⟩)) =
    actualHighCoordinates reflected left second first g.datum.C g.datum.D g.datum.inactive Z Mrow
      (Real.logb Z (volume s)) amp ξ reserve ε 2 - ε + Real.logb Z (normValue u₀) +
      (Real.logb Z 4 + 2*(N : ℝ)*Real.logb Z b + ξ/2) := by
    have h := depth_two_scale_identity reflected left second u₀ (fun l => (hunit l).unit)
      ⟨first, (g.datum.C, g.datum.D), g.datum.inactive⟩ hfirst₁ hfirst₂ hfirst (by rw [hfun]; exact hmult)
      Z (volume s) Mrow (Real.logb Z (volume s)) amp ξ reserve ε b N hZ (volume_pos s) hb hfit
    rw [hfun] at h
    exact h
  change Real.logb Z (retainedScale g.datum.radius g.datum.C g.datum.D g.datum.inactive) +
    Real.logb Z (normValue (childMultiplier left u₀ unit ⟨first, (g.datum.C, g.datum.D), g.datum.inactive⟩)) ≤ _
  rw [hradius]
  exact hid.le

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_live_main_row_scale_relative
