import Candidate.Research.RecursiveAffine.RegionalLowSource

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open HeckeFamily CenteredMomentEnergyState

/-- The native root domain `NaturalState Z 0 bPhi` has exactly zero
logarithmic puncture budget. The fixed bad mask is a different field and
is not removed. This does not claim the same for arbitrary root mask cap20. -/
theorem zero_mask_state_puncture_log {Z bΦ : ℝ} (s : NaturalState Z 0 bΦ) :
    Real.logb Z (s.puncture.absNorm : ℝ) = 0 := by
  have hu : (s.puncture.absNorm : ℝ) ≤ 1 := by simpa only [Real.rpow_zero] using s.puncture_bound
  have hl : (1 : ℝ) ≤ (s.puncture.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero)
  rw [le_antisymm hu hl, Real.logb_one]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.zero_mask_state_puncture_log
