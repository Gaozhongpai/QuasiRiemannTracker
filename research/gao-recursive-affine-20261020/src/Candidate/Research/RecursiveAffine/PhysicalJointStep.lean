/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.CorrectedJointBudget

set_option autoImplicit false
namespace Cycle153
noncomputable section

/-- One actual source-payment attachment. Every first-source missing
radical X1 is present with coefficient one. Child density and scale are
transported through the native multiplier identity, and the actual extra
volume reduction e is credited once. No child count or energy estimate is
constructed by this algebraic lemma. -/
theorem physical_prefix_attachment
    (rho delta cost X0 X1 X2 X3 m A a small Gamma scale Lv
      exponent miss row length childAmp childLoss D extraVolume
      scalePad volumePad deletionCost : ℝ)
    (hrho : 0≤rho) (hdelta : 0≤delta)
    (hparent : X0+X1+rho*X2+delta*X3≤
      small-(m*(1-rho)-delta*A-a*cost)-Gamma)
    (hchild : (exponent-scale)+miss+rho*(row-Lv)≤
      childLoss-(scale*(1-rho)-delta*length-childAmp*cost))
    (hscale : scale+Lv≤X2+scalePad)
    (hvolume : length≤X3-D-extraVolume+volumePad) :
    X0+X1+exponent+miss+rho*row+deletionCost≤
      small+childLoss-m*(1-rho)+delta*(A-D)+cost*(a+childAmp)-
        (Gamma+delta*extraVolume)+rho*scalePad+delta*volumePad+deletionCost := by
  have hs := mul_le_mul_of_nonneg_left hscale hrho
  have hv := mul_le_mul_of_nonneg_left hvolume hdelta
  nlinarith only [hparent,hchild,hs,hv]

/-- The actual valuation-cone common payment and the literal extra volume
reduction pay the corrected aggregate coefficient. Negative padding is
charged at h; common reduction and residual F are never counted twice. -/
theorem corrected_source_credit
    (delta h S extra V Red F pad Gamma : ℝ)
    (hh : 0≤h) (hF : 0≤F) (hvolume : F-pad≤extra)
    (hcoordinates : V+Red=S+extra)
    (hGamma : (delta-h)*S≤Gamma) :
    (delta-h)*(V+Red)≤Gamma+delta*extra+h*pad := by
  have he := mul_le_mul_of_nonneg_left hvolume hh
  have hf := mul_nonneg hh hF
  rw [hcoordinates]
  nlinarith only [he,hf,hGamma]

end
end Cycle153

#print axioms Cycle153.physical_prefix_attachment
#print axioms Cycle153.corrected_source_credit
