/- Copyright (c) 2026 Hailey Collet; generalization (c) 2026 Zhongpai Gao.
Released under Apache 2.0. Based on the native LowChildFactsRow proof.
The terminal bin is only required to lie above the native density floor;
the physical common saving is retained rather than dropped. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildFactsRow

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentSectorLocalization CenteredMomentCommonRadialData
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle63FinalCapacity Cycle63Moment Cycle63InitialMass

/-- A genuine native row payment for every later terminal bin above the
density floor, retaining its common-ideal saving gamma. All four actual
coordinates, including the missing radical coordinate X1 with coefficient
one, remain in highExponentValue; no historical missing ideal is replaced
by a width coordinate. -/
theorem regional_actual_row_payment
    (reflected second : Bool) (l : FirstSourceLabel) (hC : Supported l.1.1)
    (hD : Supported l.1.2) (heq : primeSupport l.1.1 = primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (Z δ Mrow A amp ξ reserve ε σbar : ℝ) (hZ : 1 < Z)
    (hδ : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ 3/4)
    (hω : 0 ≤ frequencyLoss Z 32 ξ + reserve) (hε : 0 ≤ ε)
    (hside : lowLabelSide reflected Z A l ≤ σbar) :
    let γ := ValuationCone.commonRate δ *
      (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) +
        Real.logb Z ((if second then D₂ else C₂).absNorm : ℝ))
    0 ≤ γ ∧
    highExponentValue δ
      (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z Mrow A amp ξ reserve ε) ≤
      σbar + (frequencyLoss Z 32 ξ + reserve + ε + max (1 - Mrow) 0) -
        (1 * (1 - LocalMoment.unmarkedDensity δ) - δ * A -
          amp * (5 - 6 * LocalMoment.unmarkedDensity δ)) - γ := by
  have hh := actual_high_coordinate_allocation_payment_reserve_E reflected second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z δ Mrow A amp ξ reserve ε hZ hδ
  obtain ⟨hρlo, hρhi, -⟩ := Cycle63.Physical.high_density_bounds hδ
  have hρ0 : 0 ≤ LocalMoment.unmarkedDensity δ := by linarith
  have hρ1 : LocalMoment.unmarkedDensity δ ≤ 1 := by
    have := Cycle63.Arithmetic.rho0_bounds.2
    linarith
  have hγ := Cycle63.Physical.commonRate_nonneg hδ
  have hc : 0 ≤ Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) :=
    Real.logb_nonneg hZ (by cases reflected <;> exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (by first | exact hC.1 | exact hD.1)))
  have hb₂ : 0 ≤ Real.logb Z ((if second then D₂ else C₂).absNorm : ℝ) :=
    Real.logb_nonneg hZ (by cases second <;> exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (by first | exact hC₂.1 | exact hD₂.1)))
  have hγc := mul_nonneg hγ (add_nonneg hc hb₂)
  have h1 : (1 - Mrow) * (1 - LocalMoment.unmarkedDensity δ) ≤ max (1 - Mrow) 0 := by
    rcases le_total (1 - Mrow) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hρ1)]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg h hρ0]
  have h2 : (1 - LocalMoment.unmarkedDensity δ) * (frequencyLoss Z 32 ξ + reserve) ≤
      frequencyLoss Z 32 ξ + reserve := by
    nlinarith [mul_nonneg hρ0 hω]
  have h3 : LocalMoment.unmarkedDensity δ * ε ≤ ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) hε]
  dsimp only at hh ⊢
  refine ⟨hγc, ?_⟩
  unfold lowLabelSide lowConeSurplus at hside
  linarith only [hh, hside, h1, h2, h3]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.regional_actual_row_payment
