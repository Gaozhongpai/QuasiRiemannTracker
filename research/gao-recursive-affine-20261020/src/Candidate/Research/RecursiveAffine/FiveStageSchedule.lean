/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalStageSchedule
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Cycle153.RegionalSchedule
noncomputable section
open scoped Classical ContDiff
open Filter Set
open OAI.SevenEighths OAI.SevenEighths.Cycle63InitialMass
open OAI.SevenEighths.Cycle63Moment OAI.SevenEighths.Cycle63MarkedPlain
open OAI.SevenEighths.LocalMoment OAI.SevenEighths.CenteredMomentSectorLocalization

abbrev StageSubset (α : Type*) := Fin 5 × Finset α

variable {α : Type*} [Fintype α]
variable (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
variable (ε B L : ℝ) (hε : 0<ε) (hB : 0≤B) (hL : 0≤L)
variable (bound : StageSubset α→ℕ→ℝ) (hbound : ∀i k,0≤bound i k)
variable (J : StageSubset α→ℕ) (cap : ℝ) (hcap : 0<cap)

/-- Native analytic data for every actual subset and all five stages.
The count is the single fixed ambient slot count; no moving type enters
this choice. -/
def fivePreliminary (i : StageSubset α) : HighSourceParameters :=
  preliminary (stage i.1) W hWs hW ε B L (Fintype.card α) (bound i)
    hε hB hL (hbound i)

def fiveMu (i : StageSubset α) : ℝ := stageMu (stage i.1) ε

/-- Degrees are supplied by the actual fixed-dictionary HIGH count before
this common cutoff is chosen. All later source/height data are quantified
after the cutoff. -/
def fiveHeight : ℝ :=
  markedHeight (commonHeight (fivePreliminary W hWs hW ε B L hε hB hL bound hbound) J (fiveMu ε) cap)

include hcap

theorem fiveHeight_pos : 0<fiveHeight W hWs hW ε B L hε hB hL bound hbound J cap :=
  (marked_height_gates _ (commonHeight_gates _ J (fiveMu ε) cap
    (fun i=>stageMu_pos (stage i.1) hε) hcap
    (fun i=>(fivePreliminary W hWs hW ε B L hε hB hL bound hbound i).hεs)
    (fun i=>preliminary_positive_plain (stage i.1) W hWs hW ε B L (Fintype.card α) (bound i) hε hB hL (hbound i))).1).1

/-- The schedule at stage j has cutoff τ/8^j. Every other field is the
literal native schedule of that source's own profile-bound function. -/
def fiveHigh (i : StageSubset α) : HighSourceParameters :=
  withHeight (fivePreliminary W hWs hW ε B L hε hB hL bound hbound i)
    (depthHeight (fiveHeight W hWs hW ε B L hε hB hL bound hbound J cap) i.1)
    (depthHeight_pos (fiveHeight_pos W hWs hW ε B L hε hB hL bound hbound J cap hcap) i.1)

/-- Both native analytic height gates and the actual density polynomial
are paid for every stage/subset by the same initial cutoff choice. -/
theorem fiveHigh_gates (i : StageSubset α) :
    2*(fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ<
      (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).d*
      (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).vslot ∧
    8*(fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ≤
      (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).d*
      (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).vslot ∧
    16*(fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ≤
      (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).d*
      (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).vplain ∧
    2*(fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ*((J i:ℝ)+1)≤fiveMu ε i/8 := by
  have hg := (commonHeight_gates
    (fivePreliminary W hWs hW ε B L hε hB hL bound hbound) J (fiveMu ε) cap
    (fun i=>stageMu_pos (stage i.1) hε) hcap
    (fun i=>(fivePreliminary W hWs hW ε B L hε hB hL bound hbound i).hεs)
    (fun i=>preliminary_positive_plain (stage i.1) W hWs hW ε B L (Fintype.card α) (bound i) hε hB hL (hbound i))).2.2 i
  have hold := (commonHeight_gates
    (fivePreliminary W hWs hW ε B L hε hB hL bound hbound) J (fiveMu ε) cap
    (fun i=>stageMu_pos (stage i.1) hε) hcap
    (fun i=>(fivePreliminary W hWs hW ε B L hε hB hL bound hbound i).hεs)
    (fun i=>preliminary_positive_plain (stage i.1) W hWs hW ε B L (Fintype.card α) (bound i) hε hB hL (hbound i))).1
  have hm := (marked_height_gates _ hold).2.1
  have hle := (depthHeight_le
    (fiveHeight_pos W hWs hW ε B L hε hB hL bound hbound J cap hcap).le i.1).trans hm
  change 2*depthHeight _ i.1<_ ∧ 8*depthHeight _ i.1≤_ ∧
    16*depthHeight _ i.1≤_ ∧ 2*depthHeight _ i.1*((J i:ℝ)+1)≤_
  have h2 := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ)≤2)
  have h8 := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ)≤8)
  have h16 := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ)≤16)
  have hJ : 0≤(J i:ℝ)+1 := by positivity
  exact ⟨h2.trans_lt hg.2.1,h8.trans hg.2.2.1,h16.trans hg.2.2.2.1,
    (mul_le_mul_of_nonneg_right h2 hJ).trans hg.2.2.2.2⟩

/-- The extra genuine marked-plain witness gates are retained. The bound
is on the same subset type, without replacing its Fourier dimension. -/
theorem fiveHigh_marked (hμcap : ∀j : Fin 5,stageMu (stage j) ε≤Cycle63.Optimization.geometryLossCap)
    (i : StageSubset α) :
    MarkedSchedule (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i)
      (Fintype.card i.2) W (33/50) (33/50) := by
  have hold := (commonHeight_gates
    (fivePreliminary W hWs hW ε B L hε hB hL bound hbound) J (fiveMu ε) cap
    (fun i=>stageMu_pos (stage i.1) hε) hcap
    (fun i=>(fivePreliminary W hWs hW ε B L hε hB hL bound hbound i).hεs)
    (fun i=>preliminary_positive_plain (stage i.1) W hWs hW ε B L (Fintype.card α) (bound i) hε hB hL (hbound i))).1
  have hm := marked_height_gates _ hold
  have hle := depthHeight_le
    (fiveHeight_pos W hWs hW ε B L hε hB hL bound hbound J cap hcap).le i.1
  have hz : (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ< markedCoreMin/2 :=
    hle.trans_lt hm.2.2.1
  have hw : 4*(fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ<
      markedCoreMin*markedWitnessRate :=
    (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ)≤4)).trans_lt hm.2.2.2
  let P := fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i
  have he : P.e≤fiveMu ε i/294912 := by
    change highBuffer 1 1 _ (geometryFinalPlainRate (fiveMu ε i) 31)≤fiveMu ε i/294912
    have hh := (min_le_right (1/2000:ℝ) _).trans
      (min_le_right (geometryFinalDictionaryRate (fiveMu ε i) 31 3 4 3 B L (Fintype.card α)/(32*(1+1)))
        (geometryFinalPlainRate (fiveMu ε i) 31/(48*(1+2))))
    change highBuffer 1 1 _ _≤_ at hh
    convert hh using 1 <;> norm_num [geometryFinalPlainRate,fiveMu] <;> ring
  have hs := marked_slot_loss_gate (fiveMu ε i)
    (geometryFinalDictionaryRate (fiveMu ε i) 31 3 4 3 B L (Fintype.card α))
    (Fintype.card α) (hμcap i.1) (min_le_right _ _)
  have hh : MarkedSchedule P (Fintype.card α) W (33/50) (33/50) :=
    ⟨rfl,rfl,le_rfl,le_rfl,rfl,by norm_num [P,fiveHigh,withHeight,fivePreliminary,preliminary,geometryAffineFinalHighSchedule,highParameters],
      hz,hw,marked_buffer_budget (fiveMu ε i) P.e (hμcap i.1) he,hs⟩
  exact hh.of_card_le (Fintype.card_le_of_injective (fun x : i.2=>x.val) Subtype.val_injective)

/-- Matching actual LOW schedule at the same stage. Its δ, e and κ are
shared with HIGH; no desired energy inequality is used to construct it. -/
def fiveLow (i : StageSubset α) : GeometryAffineLowSchedule :=
  lowSchedule (stage i.1) W hWs hW ε B L (Fintype.card α) (bound i)
    hε hB hL (hbound i)
    (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).τ
    (fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i).hτ
    (fiveHigh_gates W hWs hW ε B L hε hB hL bound hbound J cap hcap i).1

/-- One actual native LOW schedule serves every subset at a fixed stage.
Only the retained profile bound of HIGH depends on the subset. -/
theorem fiveLow_subset_independent (j : Fin 5) (T T' : Finset α) :
    fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j,T)=
      fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j,T') := rfl

/-- The next actual source cutoff meets the native half-height-cap gate. -/
theorem fiveLow_next_height (j : Fin 4) (T T' : Finset α) :
    (fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j.succ,T')).τ<
      (fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j.castSucc,T)).τ/2 := by
  have hp := (fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j.castSucc,T)).τ_pos
  have heq : (fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j.succ,T')).τ=
      (fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap (j.castSucc,T)).τ/8 :=
    depthHeight_next _ j
  rw [heq]
  linarith

/-- Every rounded ledger at this stage has precisely the μ consumed by
its actual native LOW/HIGH schedule, independent of the moving grid cell. -/
theorem fiveLow_mu_native (i : StageSubset α) (Ngrid : ℕ)
    (cell : RegionalIndex (stage i.1) Ngrid) :
    (fiveLow W hWs hW ε B L hε hB hL bound hbound J cap hcap i).μ=
      @geometryLossUnit (regionalFamily (stage i.1) Ngrid cell) 1 ε := rfl

/-- One eventual threshold covers the two literal native truncated-height
gates, the actual density polynomial, localization losses and all actual
buffered bins at every stage/subset. This threshold precedes all moving
heights, physical sources and natural states. -/
theorem five_native_threshold :
    ∀ᶠ Z : ℝ in atTop, ∀i : StageSubset α,
      let P := fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i
      1<Z ∧ 2<Z^P.τ ∧
      (∀p : BufferIndex P.e,(p.1.val:ℝ)≤Z^P.τ) ∧
      0≤frequencyLoss Z 32 (fiveMu ε i/64)+fiveMu ε i/8 ∧
      frequencyLoss Z 32 (fiveMu ε i/64)+fiveMu ε i/8≤33*fiveMu ε i/128 ∧
      ∀k : ℕ,(k:ℝ)≤Z^P.τ →
        (3+(3*k+2:ℕ)*Z^P.τ)^2≤(Z^P.d)^P.vslot ∧
        (3+(3*k+2:ℕ)*Z^P.τ)^4≤(Z^P.d)^P.vplain ∧
        (1+3*(k+1:ℕ)*Z^P.τ)^(J i)≤Z^(fiveMu ε i/8) := by
  apply Filter.eventually_all.2
  intro i
  let P := fiveHigh W hWs hW ε B L hε hB hL bound hbound J cap hcap i
  have hg := fiveHigh_gates W hWs hW ε B L hε hB hL bound hbound J cap hcap i
  filter_upwards [eventually_high_truncated_heights P (J i) (fiveMu ε i/8) hg.2.1 hg.2.2.1 hg.2.2.2,
    eventually_geometry_zero_heights P.e P.τ P.hτ,
    eventual_geometry_small_frequency (fiveMu ε i) (stageMu_pos (stage i.1) hε)] with Z hz hb hf
  exact ⟨hz.1,hb.2.1,hb.2.2,hf.2.1,hf.2.2,hz.2⟩

end
end Cycle153.RegionalSchedule

#print axioms Cycle153.RegionalSchedule.fiveHigh_gates
#print axioms Cycle153.RegionalSchedule.fiveHigh_marked
#print axioms Cycle153.RegionalSchedule.fiveLow_subset_independent
#print axioms Cycle153.RegionalSchedule.fiveLow_next_height
#print axioms Cycle153.RegionalSchedule.fiveLow_mu_native
#print axioms Cycle153.RegionalSchedule.five_native_threshold
