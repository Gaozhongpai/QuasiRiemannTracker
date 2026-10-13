import Candidate.Main

namespace QRH
open scoped _root_.DirichletCharacter

theorem canonical_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8748673 / 10000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Candidate.bound χ hs hpole

end QRH

namespace QRH
theorem zeta_bound (s : ℂ) (hs : (8748673 / 10000000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  exact Submission20261012.Global.zeta_nonzero s hs
theorem hecke_bound (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (8748673 / 10000000 : ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact Submission20261012.Global.hecke_nonzero χ s hs hpole
end QRH
