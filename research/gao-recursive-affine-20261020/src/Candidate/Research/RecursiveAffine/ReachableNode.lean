/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableGeometry
import Candidate.Research.RecursiveAffine.RegionalStageSchedule
import Candidate.Research.RecursiveAffine.PrefixHighPresentation
import Candidate.Research.RecursiveAffine.DepthReturnedFamily
import Candidate.Research.RecursiveAffine.DecoratedHistory
import Candidate.Research.RecursiveAffine.ActualFamilyRebase
import Candidate.Cycle63.Physical.InitialSourceReduction

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open HeckeFamily RayFourExpansion CenteredMomentEnergyState
open CenteredMomentEnergyBands QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentInductionEnergy
open Cycle63InitialSource Cycle63Moment Cycle153HighProvider Cycle153SourceReturn
open Cycle153JointCount Cycle153ReachableGeometry Cycle153Geometry

/-- The first inner state has already passed the root two-ray transform. -/
def PrefixBase : ℕ → Type
  | 0 => RayCharacter × RayCharacter
  | n+1 => PrefixBase n × (RayCharacter × RayCharacter)

def prefixDictionary : (n : ℕ) → Character → PrefixBase n → Character
  | 0, η => secondFixedDictionary η
  | n+1, η => extendFixedDictionary (prefixDictionary n η)

/-- A terminal HIGH consumes one additional two-ray dictionary. -/
def SuffixDepth : ℕ → Type
  | 0 => Empty
  | n+1 => Option (SuffixDepth n)

instance suffixFintype : (n : ℕ) → Fintype (SuffixDepth n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n+1 => by
    letI := suffixFintype n
    exact inferInstanceAs (Fintype (Option (SuffixDepth n)))

def innerStage (n : ℕ) : Cycle153.RegionalStage :=
  match n with
  | 0 => Cycle153.FixedStages.stage1
  | 1 => Cycle153.FixedStages.stage2
  | 2 => Cycle153.FixedStages.stage3
  | _ => Cycle153.FixedStages.stage4

def modelUnit (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.U1 x, Coordinates.U2 x, Coordinates.U3 x, Coordinates.U4 x] j

def modelLength (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.A1 x, Coordinates.A2 x, Coordinates.A3 x, Coordinates.A4 x] j

def modelSlots (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.z1 x, Coordinates.z2 x, Coordinates.z3 x, Coordinates.z4 x] j

def suffixJunction : (start count : ℕ) → SuffixDepth count → ℝ
  | _, 0 => fun d => nomatch d
  | start, count+1 => fun d => match d with
    | none => (innerStage start).q
    | some d => suffixJunction (start+1) count d

def suffixBase : (start count : ℕ) → SuffixDepth count → Type
  | _, 0 => fun d => nomatch d
  | start, count+1 => fun d => match d with
    | none => PrefixBase (start+1)
    | some d => suffixBase (start+1) count d

def suffixDictionary : (start count : ℕ) → (d : SuffixDepth count) →
    Character → suffixBase start count d → Character
  | _, 0 => fun d => nomatch d
  | start, count+1 => fun d => match d with
    | none => prefixDictionary (start+1)
    | some d => suffixDictionary (start+1) count d

def suffixOffset : (count : ℕ) → SuffixDepth count → ℕ
  | 0, d => nomatch d
  | _+1, none => 0
  | count+1, some d => suffixOffset count d+1

theorem suffixOffset_lt : ∀ count (d : SuffixDepth count), suffixOffset count d < count
  | 0, d => nomatch d
  | count+1, none => by simp only [suffixOffset]; omega
  | count+1, some d => by
    have h := suffixOffset_lt count d
    simp only [suffixOffset]
    omega

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Data fixed before any moving daughter state. Surviving slots always
refer to this original ray dictionary; a continuation only divides their
original exponents by its actual unit. -/
structure SourceContext where
  globalBase : ℝ
  globalBase_gt_one : 1 < globalBase
  etaSeed : Character
  Q : Ideal O
  Q_le_M : Q ≤ M
  fixed_small : internalQ Q etaSeed ≤ Ideal.span {(72:O)}
  W : ℝ → ℂ
  W_smooth : ContDiff ℝ ∞ W
  W_support : Function.support W ⊆ Set.Icc (1:ℝ) 2
  theta : α → RayQuotient.Characters M H
  originalWeight : α → ℝ
  originalWeight_nonneg : ∀ i, 0 ≤ originalWeight i
  sigma : α → ℝ
  sigma_fixed : ∀ i, sigma i ∈ Set.Icc (33/50:ℝ) (33/50)
  frequency : α → ℝ
  gridDenominator : ℕ
  grid_positive : 0 < gridDenominator
  Bnorm : ℝ
  normCap_nonneg : 0 ≤ Bnorm
  Tz : ℝ

variable {M H hH}

abbrev SuffixFamily (start count : ℕ) (eta : Character) (Z Bnorm Tz : ℝ) (root : O) :=
  DepthReturnedFamily M H hH (suffixJunction start count) (suffixBase start count)
    (suffixDictionary start count) eta Z Bnorm Tz root

theorem suffixFamily_transport_value {start count : ℕ} {eta : Character}
    {Z Z' Bnorm Tz : ℝ} {root : O} (he : Z = Z')
    (F : SuffixFamily (hH:=hH) start count eta Z Bnorm Tz root) :
    (he ▸ F).value = F.value := by
  cases he
  rfl

/-- The recursive dictionaries are definitionally the dictionaries of
the native attachment operator; no cast of HIGH witnesses is introduced. -/
def attachSuffixFamily {I : Type} [Fintype I] {start count : ℕ}
    {eta : Character} {Z Bnorm Tz : ℝ} {root : O}
    (own : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z Bnorm Tz root)
    (ownWeight : ℝ) (hOwnWeight : 0 ≤ ownWeight)
    (childRoot : I → O) (hChildRoot : ∀ r, root ∣ childRoot r)
    (children : (r : I) → SuffixFamily (hH:=hH) (start+1) count eta Z Bnorm Tz (childRoot r))
    (edge missing : I → ℝ) (hEdge : ∀ r, 0 ≤ edge r) (hMissing : ∀ r, 0 ≤ missing r) :
    SuffixFamily (hH:=hH) start (count+1) eta Z Bnorm Tz root := by
  let A := DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children
    edge missing hEdge hMissing
  exact {
    Prefix := A.Prefix
    prefixFintype := A.prefixFintype
    multiplier := A.multiplier
    root_divides := A.root_divides
    historyMissing := A.historyMissing
    historyMissing_nonneg := A.historyMissing_nonneg
    part := fun d => by
      cases d with
      | none => exact A.part none
      | some d => exact A.part (some d)
    weight := A.weight
    weight_nonneg := A.weight_nonneg }

theorem attachSuffixFamily_value {I : Type} [Fintype I] {start count : ℕ}
    {eta : Character} {Z Bnorm Tz : ℝ} {root : O}
    (own : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z Bnorm Tz root)
    (ownWeight : ℝ) (hOwnWeight : 0 ≤ ownWeight)
    (childRoot : I → O) (hChildRoot : ∀ r, root ∣ childRoot r)
    (children : (r : I) → SuffixFamily (hH:=hH) (start+1) count eta Z Bnorm Tz (childRoot r))
    (edge missing : I → ℝ) (hEdge : ∀ r, 0 ≤ edge r) (hMissing : ∀ r, 0 ≤ missing r) :
    (attachSuffixFamily own ownWeight hOwnWeight childRoot hChildRoot children
      edge missing hEdge hMissing).value = ownWeight*own.value + ∑ r, edge r*(children r).value := by
  calc
    _ = (DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children
      edge missing hEdge hMissing).value := by
        unfold DepthReturnedFamily.value
        apply Finset.sum_congr (Finset.ext (fun d =>
          ⟨fun _ => Finset.mem_univ d, fun _ => Finset.mem_univ d⟩))
        intro d hd
        cases d <;> rfl
    _ = _ := DepthReturnedFamily.value_attach own ownWeight hOwnWeight childRoot hChildRoot children
      edge missing hEdge hMissing

/-- An actual reachable inner source. There is no energy estimate,
returned count, child family, or desired endpoint among its fields. The
physical child constructor must supply the literal prefix and source
geometry; only the inequalities visible at the present depth are kept. -/
structure ReachableNode (C : SourceContext (α:=α) M H) (j : Fin 4) where
  coordinates : Fin 14 → ℝ
  prefixRows : PrefixRows (j.val+1) coordinates
  unit : ℝ
  unit_eq : unit = modelUnit j coordinates
  unit_floor : (1/50:ℝ) ≤ unit
  unit_le_one : unit ≤ 1
  localBase : ℝ
  localBase_eq : localBase = C.globalBase^unit
  slots : Finset α
  state : NaturalState localBase 20 2
  fixedModulus : state.fixedModulus = internalQ C.Q C.etaSeed
  width_le_one : state.width ≤ 1
  presentation : PrefixHighPresentation (prefixDictionary j.val C.etaSeed)
    state.character state.puncture
  profiles : Profiles (1/4) (9/4)
  X1 : ℝ
  X2 : ℝ
  X1_pos : 0 < X1
  X2_pos : 0 < X2
  length_eq : unit*(length localBase X1+length localBase X2+
    ∑ i : slots, C.originalWeight i/unit) = modelLength j coordinates
  slots_eq : (∑ i : slots, C.originalWeight i) = modelSlots j coordinates
  t : ℝ
  height : ℝ
  height_nonneg : 0 ≤ height
  frequency_bound : ∀ i : slots, |C.frequency i| ≤ height
  plane : ℝ
  position : Cycle153.RegionalPosition
  rounded : position = Cycle153.roundedPosition (1/C.gridDenominator) plane
    (length localBase X1) (length localBase X2)
    (∑ i : slots, C.originalWeight i/unit)
  positionFacts : position.Facts (innerStage j.val)
  weight_mesh : ∀ i : slots, C.originalWeight i/unit ≤ 1/C.gridDenominator
  window : @Cycle63.AffineLedger.PlainWindow
    (Cycle153.regionalLedger (innerStage j.val) position positionFacts)
    (length localBase X1) (length localBase X2)
    (∑ i : slots, C.originalWeight i/unit)
  overshoot : length localBase X1 + length localBase X2 +
    6*Cycle63.Optimization.slotPrice*(∑ i : slots, C.originalWeight i/unit) ≤ 1+9/1000

namespace ReachableNode
variable {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
variable (hH)

theorem unit_pos : 0 < N.unit := lt_of_lt_of_le (by norm_num) N.unit_floor

theorem localBase_gt_one : 1 < N.localBase := by
  rw [N.localBase_eq]
  exact Real.one_lt_rpow C.globalBase_gt_one N.unit_pos

@[instance_reducible] def ledger : Cycle63.AffineLedger :=
  Cycle153.regionalLedger (innerStage j.val) N.position N.positionFacts

/-- The same actual affine input used by the HIGH provider and AtState. -/
def input : Input N.slots := by
  letI := N.ledger
  exact affineInput M H hH C.etaSeed (fun i => C.theta i) C.W C.W_smooth.continuous
    1 2 (33/50) (33/50) (by norm_num) C.W_support
    (fun i => C.originalWeight i/N.unit) (fun i => C.sigma i) (fun i => C.frequency i)
    (fun i => C.sigma_fixed i) N.state N.profiles (by norm_num)
    (Cycle63.AffineLedger.comparisonLength
      (length N.localBase N.X1) (length N.localBase N.X2)
      (∑ i : N.slots, C.originalWeight i/N.unit)) N.t N.X1 N.X2 N.X1_pos N.X2_pos

def sourceEnergy : ℝ :=
  energy (N.input hH).η N.state.mask 1 (N.input hH).t (N.input hH).W₁ (N.input hH).W₂
    (N.input hH).slots (N.input hH).coefficient (N.input hH).P (N.input hH).X₁ (N.input hH).X₂
    N.state.radial.keep N.state.radial.profile N.state.radial.scale

abbrev Family := SuffixFamily (hH:=hH) j.val (4-j.val)
  C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult

theorem localBase_relative {k : Fin 4} (child : ReachableNode C k) :
    child.localBase = N.localBase^(child.unit/N.unit) := by
  rw [N.localBase_eq,child.localBase_eq]
  rw [← Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]
  congr 1
  field_simp [ne_of_gt N.unit_pos]

/-- Exact base transport of the entire selected child forest. Its
weights, records, source keys and root multiplier are retained, its value
is unchanged, and Bnorm is the same fixed cap. -/
def rebaseChildFamily {k : Fin 4} (child : ReachableNode C k)
    (hunit : child.unit ≤ N.unit) (F : child.Family hH) :
    SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed N.localBase C.Bnorm C.Tz
      child.presentation.mult := by
  have hF : SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed
      (N.localBase^(child.unit/N.unit)) C.Bnorm C.Tz child.presentation.mult :=
    (N.localBase_relative child) ▸ F
  exact Cycle153RegionalLow.rebaseDepthReturnedFamily N.localBase_gt_one
    (div_pos child.unit_pos N.unit_pos) ((div_le_one N.unit_pos).mpr hunit)
    C.normCap_nonneg hF

theorem rebaseChildFamily_value {k : Fin 4} (child : ReachableNode C k)
    (hunit : child.unit ≤ N.unit) (F : child.Family hH) :
    (N.rebaseChildFamily hH child hunit F).value = F.value := by
  unfold rebaseChildFamily
  rw [Cycle153RegionalLow.rebaseDepthReturnedFamily_value]
  exact suffixFamily_transport_value (N.localBase_relative child) F

end ReachableNode

variable (hH)

/-- A finite orientation word is part of the literal path code. Source
maximizers may choose different reflections on different physical rows;
the provenance never assumes a common orientation for unrelated rows. -/
abbrev OrientationWord := Fin 4 → Bool

def wordLeft (word : OrientationWord) (k : ℕ) : Bool := word ⟨k%4,Nat.mod_lt _ (by norm_num)⟩

/-- Literal chronology, with only the sixteen possible orientation words
as an extra fixed finite partition. Residual allocations and deleted
subsets are selected source metadata, not additional path coordinates. -/
structure ForestChronology
    {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
    (F : N.Family hH) (Bsrc : ℝ) (boxes : ℕ → Finset (Fin 4 → ℤ)) where
  word : (d : SuffixDepth (4-j.val)) → F.Prefix d → OrientationWord
  units : OrientationWord → ∀ k, History k → FirstSourceLabel → O
  code : (d : SuffixDepth (4-j.val)) → F.Prefix d → History (suffixOffset (4-j.val) d)
  injective : ∀ d, Function.Injective (fun p => (word d p,code d p))
  multiplier : ∀ d p, F.multiplier d p =
    historyMultiplier (units (word d p)) (wordLeft (word d p)) N.presentation.mult
      (suffixOffset (4-j.val) d) (code d p)
  missing : ∀ d p, F.historyMissing d p =
    historyMissing (wordLeft (word d p)) N.localBase (suffixOffset (4-j.val) d) (code d p)
  facts : ∀ d p, HistoryFacts (units (word d p)) (wordLeft (word d p))
    N.presentation.mult N.localBase Bsrc boxes (suffixOffset (4-j.val) d) (code d p)

/-- Constants belong outside the moving source. The returned family
already contains every raw HIGH normalizer and LOW edge; no row-scale
factor is appended to its value here. -/
structure NodeOutput
    {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
    (constant ε Bsrc : ℝ) (control : Finset (ℕ×ℕ)) (degree : ℕ)
    (boxes : ℕ → Finset (Fin 4 → ℤ)) where
  family : N.Family hH
  chronology : ForestChronology hH N family Bsrc boxes
  energy : N.sourceEnergy hH ≤
    constant*diagonalControl N.state.radial.profile*(N.profiles.control control)^2*
      (1+|N.t|+N.height)^degree*(N.localBase^(1+ε)+family.value)

/-- The strict-depth callback expected by the actual LOW producer. This
is a definition of the induction objective, not a theorem assuming the
endpoint. The finite backward proof must construct these outputs. -/
def StrictDepthIH (C : SourceContext (α:=α) M H) (j : Fin 4)
    (constant ε Bsrc : Fin 4 → ℝ) (control : Fin 4 → Finset (ℕ×ℕ))
    (degree : Fin 4 → ℕ) (boxes : Fin 4 → ℕ → Finset (Fin 4 → ℤ)) : Prop :=
  ∀ k : Fin 4, j.val < k.val → ∀ N : ReachableNode C k,
    Nonempty (NodeOutput hH N (constant k) (ε k) (Bsrc k) (control k) (degree k) (boxes k))

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.ReachableNode.localBase_gt_one
#print axioms OAI.SevenEighths.Cycle153Reachable.suffixOffset_lt
#print axioms OAI.SevenEighths.Cycle153Reachable.attachSuffixFamily_value
#print axioms OAI.SevenEighths.Cycle153Reachable.ReachableNode.rebaseChildFamily_value
