/- Copyright (c) 2026 Hailey Collet; specializations (c) 2026 Zhongpai Gao.
Released under Apache 2.0. The physical reflection and greedy-deletion
proofs are the native PR67 theorems; only the caller constants/branch cutoff
are changed. No recursive source or capacity payment is assumed proved. -/
import Candidate.Cycle63.Moment.LowBranch.Reflection
import Candidate.Cycle63.Moment.LowBranch.DirectMain

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyPaidBands
open Cycle63Moment.LowBranch
universe u
variable {α : Type u}
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual reflected LOW energy at δR=.0038 and ξR=.0001. The old
moment and genuine reflected capacity tests remain explicit native inputs. -/
theorem regional_reflected_low_incumbent [Fintype α]
    (Wslot : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ ε₀ : ℝ) (degree : ℕ)
    (S : Finset (ℕ × ℕ))
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot) (hWc : Continuous Wslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 ≤ Mcap)
    (hε : 0 ≤ ε) (hκ : 1/6 ≤ κ) (hε₀ : 0 < ε₀) :
    ∃ (Cr : ℝ) (Jexp : ℕ) (U : Finset (ℕ × ℕ)), 0 < Cr ∧ S ⊆ U ∧ degree ≤ Jexp ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (Q : Ideal O) (C₀ C₁ : ℝ), 0 ≤ C₀ → 0 ≤ C₁ →
      ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀ →
      PositiveAt (α := α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C₁ →
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap → s.width ≤ L →
      ∀ (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      ∀ (q d mesh : ℝ), 0 ≤ q → 0 ≤ d → 0 ≤ mesh → (∀ i ∈ J, w i ≤ mesh) →
      ∀ (B : α → ℝ), (∀ i ∈ J, 0 ≤ B i) →
      (∀ z, s.radial.keep z → low z → ∀ i ∈ J,
        ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ (w i)))
          (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I) t (Z ^ (w i))‖ ^ 2 ≤
          B i * Z ^ (q * w i)) →
      length Z X₁ + length Z X₂ + 6 * κ * ((∑ i ∈ J, w i) - d) ≤ s.width + (19/5000:ℝ) →
      (max 0 (s.width - length Z X₂ + (1/10000:ℝ)) + length Z X₁ + 6 * κ * ((∑ i ∈ J, w i) - d) + (19/5000:ℝ) ≤ s.width ∨
        max 0 (s.width - length Z X₁ + (1/10000:ℝ)) + length Z X₂ + 6 * κ * ((∑ i ∈ J, w i) - d) + (19/5000:ℝ) ≤ s.width) →
      ∃ R : Finset α, R ⊆ J ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : J => primePool M H bslot (Z ^ (w i)))
          (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
          (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
        ((∏ i ∈ R, B i) * Z ^ (q * (d + mesh))) *
          ((C₀ + Cr * (C₁ + 1)) * diagonalControl s.radial.profile * (p.control U) ^ 2 *
            (1 + |t| + height) ^ Jexp * Z ^ (s.width + ε + ε₀)) := by
  exact reflected_low_incumbent (α:=α) M H hH Wslot aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ
    (19/5000) (1/10000) ε₀ degree S haslot hWs hWc ha hlo hhi hbΦ hBmask hMcap hε hκ
    (by norm_num) (by norm_num) hε₀

/-- The actual physical greedy-deletion source payment on the .397 direct
branch. The native analytic theorem has no .4 cutoff. The retained-source
overshoot and its amplifier/allowance payment must still be proved. -/
theorem regional_direct_small_width [Fintype α]
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      ∀ hQM : Q ≤ M, internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh a : ℝ) (i : ℕ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀ j ∈ J, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, lo ≤ σ j) → (∀ j, σ j ≤ hi) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ (nominal δ padding amp reserve X G : ℝ),
      nominal + δ < (397/1000:ℝ) →
      s.width-nominal ≤ δ → 0 ≤ δ → 0 ≤ padding → 0 ≤ G →
      length Z X₁+length Z X₂+(6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J, w j)-nominal ≤ G+padding →
      q/(6*Cycle63.Optimization.slotPrice)*G ≤ amp+X-reserve →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        C^(Fintype.card α) *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(nominal+δ+amp-reserve+X+εold+2*ε*d*(Fintype.card α:ℝ)+
            q/(6*Cycle63.Optimization.slotPrice)*padding+q*mesh) := by
  obtain ⟨degree,S,hsource⟩ := actual_direct_low_main (α:=α) M H hH W A B ap bp bΦ Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta Rwidth dmax τ ε e κ η margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm q hq₀ hq₁
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hsource η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,C₀,C₁,hC,hC₀,hC₁,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv ha ha' hfreq hhigh
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ nominal δ padding amp reserve X G hsmall hwidth hδ hpad hG htotal hpay
  exact hZ.2 J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv ha ha' hfreq
    hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ nominal δ padding amp reserve X G hwidth hδ hpad hG htotal hpay

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.regional_reflected_low_incumbent
#print axioms OAI.SevenEighths.Cycle153RegionalLow.regional_direct_small_width
