import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell015.Parameters
import ForestUnimodality.BinomialMassData.Q31_85.Batch000_049
import ForestUnimodality.BinomialMassData.Q31_85.Batch050_099
import ForestUnimodality.BinomialMassData.Q31_85.Batch100_149
import ForestUnimodality.BinomialMassData.Q31_85.Batch150_199
import ForestUnimodality.BinomialMassData.Q19_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_51.Batch100_149
import ForestUnimodality.BinomialMassData.Q19_51.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree000.table
  base := (305636593933839151054687727/25000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (42290916841116386187815478750000000000000)
      constant := (10391644193750531135859382718000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree000.table
  base := (305636593933839151054687727/25000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (352)
      previous := (209)
      next := (0)
      square := (3214677894573955210799631670000000000000)
      linear := (8458183368223277237563095750000000000000)
      constant := (2078328838750106227171876543600000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree001.table
  base := (82352247607576462379663804421381353325643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (519635556835393342123285975210000000000000)
      constant := (118773138878611720320221252550468055555554135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree001.table
  base := (81498048356523820910256407913381353325643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (927628775356730523315995639370000000000000)
      constant := (211562571953914507728041624468064899999997443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9626951786107662983/20000000000000000000)
  directionHi := (12033689732634578729/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree002.table
  base := (28156297426586022492317186047416899961553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (320325527371808119053708811670000000000000)
      constant := (80992671274318376917953800259822840888888170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree002.table
  base := (55207255631880118035802438290111186774317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (561155495375299629284837628990000000000000)
      constant := (142902897516881838778063164849519196799998517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9626951786107662983/20000000000000000000)
  centralHi := (12033689732634578729/25000000000000000000)
  directionLo := (34036414450563370573/50000000000000000000)
  directionHi := (68072828901126741147/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree003.table
  base := (19585594584975923546016823705119198108497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (121015497908222895984131648130000000000000)
      constant := (56142860228043538248638852771442482533556330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree003.table
  base := (3808895914405673961184337905523830429307/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (21631357265985415028186624290000000000000)
      constant := (10915268339220931823314841670823869940697230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34036414450563370573/50000000000000000000)
  centralHi := (68072828901126741147/100000000000000000000)
  directionLo := (83371848077772116679/100000000000000000000)
  directionHi := (2084296201944302917/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree004.table
  base := (1734371457881694045054892036494475683639/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-78294531555362327085445515410000000000000)
      constant := (39631369689823540359755458087904277805733680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree004.table
  base := (13398542771670182446020147827985281446511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-171791064587562158777478391770000000000000)
      constant := (68862987779629803362125286259939434084750222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83371848077772116679/100000000000000000000)
  centralHi := (2084296201944302917/2500000000000000000)
  directionLo := (96269517861076629831/100000000000000000000)
  directionHi := (12033689732634578729/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree005.table
  base := (10003893069348410403324021446393803888799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-277604561018947550155022678950000000000000)
      constant := (28508851800308642493071920384378093238629110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree005.table
  base := (9604725128759762267623624416343476570349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-538264344568993052808636402150000000000000)
      constant := (49259813624484057878617710502818765118955498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96269517861076629831/100000000000000000000)
  centralHi := (12033689732634578729/12500000000000000000)
  directionLo := (53816296524624374953/50000000000000000000)
  directionHi := (107632593049248749907/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree006.table
  base := (14652332983078056097634621431337259421469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-476914590482532773224599842490000000000000)
      constant := (20907810776889797429869692832374339864022705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree006.table
  base := (3499537452050664131182949397877217511921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-100526402727824882982199379170000000000000)
      constant := (3997112848917188572643307637886063443780676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53816296524624374953/50000000000000000000)
  centralHi := (107632593049248749907/100000000000000000000)
  directionLo := (2947639956792364547/2500000000000000000)
  directionHi := (117905598271694581881/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree007.table
  base := (5428183449115346524749778917661940129777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-676224619946117996294177006030000000000000)
      constant := (15632918110892935318579714655571006975055530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree007.table
  base := (516169957763952758977428071298782871481/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-1271210904531854840870952422910000000000000)
      constant := (26821312937613775711502526277102684974441620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2947639956792364547/2500000000000000000)
  centralHi := (117905598271694581881/100000000000000000000)
  directionLo := (63676300774124878563/50000000000000000000)
  directionHi := (127352601548249757127/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree008.table
  base := (4044697802023974126017773351142471519403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-875534649409703219363754169570000000000000)
      constant := (11917612457563754131452429547409742691074670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree008.table
  base := (7652950293153519642145725532930987573239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-1637684184513285734902110433290000000000000)
      constant := (20417328454008176121263712808193498677994639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63676300774124878563/50000000000000000000)
  centralHi := (127352601548249757127/100000000000000000000)
  directionLo := (136145657802253482293/100000000000000000000)
  directionHi := (68072828901126741147/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree009.table
  base := (6010146369751104436058183308691054273457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-1074844678873288442433331333110000000000000)
      constant := (9268754720927007414516372682390573425145365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree009.table
  base := (5648285599074189130746922775908580236149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-222684162721635180992585382630000000000000)
      constant := (1764619761406700943296999712477579688247061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136145657802253482293/100000000000000000000)
  centralHi := (68072828901126741147/50000000000000000000)
  directionLo := (72202138395807472373/50000000000000000000)
  directionHi := (144404276791614944747/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree010.table
  base := (4398098332780933657172239310056232697853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-1274154708336873665502908496650000000000000)
      constant := (7367692254584610788120439102731256248397585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree010.table
  base := (4093031180873200537926723012147658521153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-2370630744476147522964426454050000000000000)
      constant := (12651272640041560874316836288096059813518953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72202138395807472373/50000000000000000000)
  centralHi := (144404276791614944747/100000000000000000000)
  directionLo := (76107736421815851793/50000000000000000000)
  directionHi := (152215472843631703587/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree011.table
  base := (1554944920866121978114712316416675346171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-1473464737800458888572485660190000000000000)
      constant := (6007267472256061871295349652156191750434190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree011.table
  base := (284793712997366814001943161231244103641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-2737104024457578416995584464430000000000000)
      constant := (10364223803943453507940757704684659135702410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76107736421815851793/50000000000000000000)
  centralHi := (152215472843631703587/100000000000000000000)
  directionLo := (31928986949360869871/20000000000000000000)
  directionHi := (39911233686701087339/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree012.table
  base := (256444719728099880505967106403543335681/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-1672774767264044111642062823730000000000000)
      constant := (5051703638403919226173110825392960960472360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree012.table
  base := (911278729917491866015190918132785923329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-344841922715445479002971386090000000000000)
      constant := (976131259263762716594848163440750263684162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31928986949360869871/20000000000000000000)
  centralHi := (39911233686701087339/25000000000000000000)
  directionLo := (83371848077772116679/50000000000000000000)
  directionHi := (166743696155544233359/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree013.table
  base := (1160850127863720345757605865632175892387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-1872084796727629334711639987270000000000000)
      constant := (4411046680661583312067193828506494164499215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree013.table
  base := (239356178663098829123225308316993640283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-3470050584420440205057900485190000000000000)
      constant := (7759470375784633753144648542570001833504332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83371848077772116679/50000000000000000000)
  centralHi := (166743696155544233359/100000000000000000000)
  directionLo := (173552341456154070551/100000000000000000000)
  directionHi := (21694042682019258819/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree014.table
  base := (395948163564299661966638391549342549533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-2071394826191214557781217150810000000000000)
      constant := (4024868449957650780855590365400799984075185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree014.table
  base := (106410007516981906082746561231191019517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-3836523864401871099089058495570000000000000)
      constant := (7183782125877327869004670052584655683527434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173552341456154070551/100000000000000000000)
  centralHi := (21694042682019258819/12500000000000000000)
  directionLo := (180103776313031628981/100000000000000000000)
  directionHi := (90051888156515814491/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree015.table
  base := (-271733167856236684518576650858227880739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-2270704855654799780850794314350000000000000)
      constant := (3851863573921013668993821425709860712332145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree015.table
  base := (-438311140422106679365635510774366409963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-466999682709255777013357389550000000000000)
      constant := (776416425056208407239935818886208107520693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180103776313031628981/100000000000000000000)
  centralHi := (90051888156515814491/50000000000000000000)
  directionLo := (186425119711683626249/100000000000000000000)
  directionHi := (149140095769346901/80000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree016.table
  base := (-862148347741481125034806469654336170883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-2470014885118385003920371477890000000000000)
      constant := (3863197827010180913200258393781484233074065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree016.table
  base := (-507418111620364063678870048463267505529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-4569470424364732887151374516330000000000000)
      constant := (7122293181233981109570784120054082436238142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186425119711683626249/100000000000000000000)
  centralHi := (149140095769346901/80000000000000000)
  directionLo := (96269517861076629831/50000000000000000000)
  directionHi := (192539035722153259663/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree017.table
  base := (-694785586891896568876184613919087310403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-157019112622468836881761684790000000000000)
      constant := (237543857150570180442281854357755157231490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree017.table
  base := (-765136477775454151126017481581203515727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3168)
      previous := (1881)
      next := (0)
      square := (28932101051165596897196685030000000000000)
      linear := (-290349629667421398893090148630000000000000)
      constant := (444250505753182058313009225756151724187538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96269517861076629831/50000000000000000000)
  centralHi := (192539035722153259663/100000000000000000000)
  directionLo := (198464695334252452173/100000000000000000000)
  directionHi := (99232347667126226087/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree018.table
  base := (-1864491041821412405518707834673310011011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-2868634944045555450059525804970000000000000)
      constant := (4361849630583293790234865812725067034089105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree018.table
  base := (-997296975204057030751956963591702121349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-589157442703066075023743393010000000000000)
      constant := (916856145406549779352117911503996173860278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198464695334252452173/100000000000000000000)
  centralHi := (99232347667126226087/50000000000000000000)
  directionLo := (204218486703380223439/100000000000000000000)
  directionHi := (2552731083792252793/1250000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree019.table
  base := (-2294837196951161721419395014555029237117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-3067944973509140673129102968510000000000000)
      constant := (4822552244916074145339828672959982752365935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree019.table
  base := (-1207690216549937297008173332189303360837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-5668890264309025569244848547470000000000000)
      constant := (9200914546825676757777873091411243916925926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204218486703380223439/100000000000000000000)
  centralHi := (2552731083792252793/1250000000000000000)
  directionLo := (209814549849908462403/100000000000000000000)
  directionHi := (52453637462477115601/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree020.table
  base := (-671693439121079887306747641116776608487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-3267255002972725896198680132050000000000000)
      constant := (5411446265043236752682331198145031202945140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree020.table
  base := (-2798564999747252812114955630759427460469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-6035363544290456463276006557850000000000000)
      constant := (10384455629793396587188648493394729175320131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209814549849908462403/100000000000000000000)
  centralHi := (52453637462477115601/25000000000000000000)
  directionLo := (215265186098497499813/100000000000000000000)
  directionHi := (107632593049248749907/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree021.table
  base := (-609044013978957366351469397344759716659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-3466565032436311119268257295590000000000000)
      constant := (6121423230974994749893466522436111047138725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree021.table
  base := (-1574457161513008182238218212044963143913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-711315202696876373034129396470000000000000)
      constant := (1309992271325826205354811351078011302818286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215265186098497499813/100000000000000000000)
  centralHi := (107632593049248749907/50000000000000000000)
  directionLo := (220581176357643444561/100000000000000000000)
  directionHi := (110290588178821722281/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree022.table
  base := (-843548715910391703541899770987940686473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-3665875061899896342337834459130000000000000)
      constant := (6946676082978088447721174856037702832186060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree022.table
  base := (-54224168380949679849280995520252875813/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-6768310104253318251338322578610000000000000)
      constant := (13407147293913352852474274756456625280664768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220581176357643444561/100000000000000000000)
  centralHi := (110290588178821722281/50000000000000000000)
  directionLo := (112886015941549240869/50000000000000000000)
  directionHi := (225772031883098481739/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree023.table
  base := (-229815432785628691558871253326790886121/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-3865185091363481565407411622670000000000000)
      constant := (7882365824060915469705797029172594712882480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree023.table
  base := (-376614480194229403839426950707444871519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-7134783384234749145369480588990000000000000)
      constant := (15227568553754062197761572389039358891790810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112886015941549240869/50000000000000000000)
  centralHi := (225772031883098481739/100000000000000000000)
  directionLo := (230846194246134097779/100000000000000000000)
  directionHi := (11542309712306704889/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree024.table
  base := (-3956612367163256034164618103224644848459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-4064495120827066788476988786210000000000000)
      constant := (8924394268795551725475594380312388193976745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree024.table
  base := (-403909975925754601607389359295081102349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-833472962690686671044515399930000000000000)
      constant := (1915992655030317013616506556677215614211390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230846194246134097779/100000000000000000000)
  centralHi := (11542309712306704889/5000000000000000000)
  directionLo := (2947639956792364547/1250000000000000000)
  directionHi := (235811196543389163761/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree025.table
  base := (-2107662039260480886408457856202642366893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-4263805150290652011546565949750000000000000)
      constant := (10069245895322780361362613728074363559679230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree025.table
  base := (-858322621001703093903000206421285811027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-7867729944197610933431796609750000000000000)
      constant := (19449997129639895578891535315491178027593865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2947639956792364547/1250000000000000000)
  centralHi := (235811196543389163761/100000000000000000000)
  directionLo := (120336897326345787289/50000000000000000000)
  directionHi := (240673794652691574579/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree026.table
  base := (-4455289734144773279718275308307953598323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-4463115179754237234616143113290000000000000)
      constant := (11313875112542793714072760764667007050423265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree026.table
  base := (-4525769018179130800243094270442274100549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-8234203224179041827462954620130000000000000)
      constant := (21840337307317991794422669443439645064472051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120336897326345787289/50000000000000000000)
  centralHi := (240673794652691574579/100000000000000000000)
  directionLo := (245440075068899434239/100000000000000000000)
  directionHi := (191750058647577683/78125000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree027.table
  base := (-2339174457984193904951092029988675491929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-4662425209217822457685720276830000000000000)
      constant := (12655623724561399250082646530820727828325190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree027.table
  base := (-4743388085386181743703272655630025444391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-955630722684496969054901403390000000000000)
      constant := (2712246564724096851916584221182922646571001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245440075068899434239/100000000000000000000)
  centralHi := (191750058647577683/78125000000000000)
  directionLo := (250115544233316350037/100000000000000000000)
  directionHi := (125057772116658175019/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree028.table
  base := (-2443058063176843496344662277702812046701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-4861735238681407680755297440370000000000000)
      constant := (14092158775465678015023884686886873185034110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree028.table
  base := (-494606819460750446676137068645397427119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-8967149784141903615525270640890000000000000)
      constant := (27155486348606183327353265425773212920634810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250115544233316350037/100000000000000000000)
  centralHi := (125057772116658175019/50000000000000000000)
  directionLo := (254705203096499514253/100000000000000000000)
  directionHi := (127352601548249757127/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree029.table
  base := (-635001763166851630937482434797468371221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-5061045268144992903824874603910000000000000)
      constant := (15621424405906294501834340154793265628685240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree029.table
  base := (-2567608298514803249087428495273591898863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-9333623064123334509556428651270000000000000)
      constant := (30072478845249820692436515848346774942114674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254705203096499514253/100000000000000000000)
  centralHi := (127352601548249757127/50000000000000000000)
  directionLo := (32401701224079776271/12500000000000000000)
  directionHi := (259213609792638210169/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree030.table
  base := (-1052260066395630641953769538256531306819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-5260355297608578126894451767450000000000000)
      constant := (17241603558632319155310352878396561308232725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree030.table
  base := (-5312075711851020120583580100887893895039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1077788482678307267065287406850000000000000)
      constant := (3684218337790266810594751469343398664333729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32401701224079776271/12500000000000000000)
  centralHi := (259213609792638210169/100000000000000000000)
  directionLo := (263644932663290803231/100000000000000000000)
  directionHi := (8238904145727837601/3125000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree031.table
  base := (-1357772152990218911241748415279870557019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-5459665327072163349964028930990000000000000)
      constant := (18951086784440243976346754902874348180430180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree031.table
  base := (-5477744369679363475071978447003845272391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-10066569624086196297618744672030000000000000)
      constant := (36409086874783510351141383197802998446511009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263644932663290803231/100000000000000000000)
  centralHi := (8238904145727837601/3125000000000000000)
  directionLo := (26800299538686536839/10000000000000000000)
  directionHi := (268002995386865368391/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree032.table
  base := (-1118073404739855783488683564027933442687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-5658975356535748573033606094530000000000000)
      constant := (20748446310018517539459067203626180876586425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree032.table
  base := (-5633195629481241579396833274892691166299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-10433042904067627191649902682410000000000000)
      constant := (39823313422891008208616987748644110276456301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26800299538686536839/10000000000000000000)
  centralHi := (268002995386865368391/100000000000000000000)
  directionLo := (136145657802253482293/50000000000000000000)
  directionHi := (272291315604506964587/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree033.table
  base := (-2870006544110412440166347493310217038927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-5858285385999333796103183258070000000000000)
      constant := (22632414117482457466867829168241472757500970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree033.table
  base := (-1444822986068057864753811744579393315373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1199946242672117565075673410310000000000000)
      constant := (4822044604904597669396183727826221327428812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136145657802253482293/50000000000000000000)
  centralHi := (272291315604506964587/100000000000000000000)
  directionLo := (2212105105219865539/800000000000000000)
  directionHi := (34564142269060399047/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree034.table
  base := (-1470201690768049003698169103079399231227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-356329142086054059951338848330000000000000)
      constant := (1447168421657476916076467396349004261382820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree034.table
  base := (-2958399108967512031632748802273260923/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3168)
      previous := (1881)
      next := (0)
      square := (28932101051165596897196685030000000000000)
      linear := (-656822909648852292924248159010000000000000)
      constant := (2772491848443279037632854082484382157562000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2212105105219865539/800000000000000000)
  centralHi := (34564142269060399047/12500000000000000000)
  directionLo := (140335731896972068093/50000000000000000000)
  directionHi := (280671463793944136187/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree035.table
  base := (-751680210839241796598605982695824964269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-6256905444926504242242337585150000000000000)
      constant := (26655791154526984593665289983236263413050360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree035.table
  base := (-755799142902971816639787270874882272267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-11532462744011919873743376713550000000000000)
      constant := (51023428081220544532530760756135449678668264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140335731896972068093/50000000000000000000)
  centralHi := (280671463793944136187/100000000000000000000)
  directionLo := (284769074173331420373/100000000000000000000)
  directionHi := (142384537086665710187/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree036.table
  base := (-6138534984474967273128901734606722545261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-6456215474390089465311914748690000000000000)
      constant := (28793306330431788552286746385805285922097855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree036.table
  base := (-6168679109877627273793191110607683091869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1322104002665927863086059413770000000000000)
      constant := (6118892733498251900545149745874379586449859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284769074173331420373/100000000000000000000)
  centralHi := (142384537086665710187/50000000000000000000)
  directionLo := (288808553583229889493/100000000000000000000)
  directionHi := (144404276791614944747/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree037.table
  base := (-6256635869448969680884161036164917504831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-6655525503853674688381491912230000000000000)
      constant := (31013615082971159124636253203809694205519205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree037.table
  base := (-3142095451688107300163978658177831332371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-12265409303974781661805692734310000000000000)
      constant := (59270790007294387705472012200998921409006058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288808553583229889493/100000000000000000000)
  centralHi := (144404276791614944747/50000000000000000000)
  directionLo := (18299519251726004221/6250000000000000000)
  directionHi := (292792308027616067537/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree038.table
  base := (-3184116609223486530940518097989139023007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-6854835533317259911451069075770000000000000)
      constant := (33316010985153155842594647366279388223509770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree038.table
  base := (-6393403367577080315240868185645002834179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-12631882583956212555836850744690000000000000)
      constant := (63624459229777434903877730305477347628300421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18299519251726004221/6250000000000000000)
  centralHi := (292792308027616067537/100000000000000000000)
  directionLo := (59344516396189276341/20000000000000000000)
  directionHi := (148361290990473190853/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree039.table
  base := (-6473762265797771047014588461994914726461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-7054145562780845134520646239310000000000000)
      constant := (35699865123372671909518565369929348220263855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree039.table
  base := (-1624184542727213117573610234243398048391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1444261762659738161096445417230000000000000)
      constant := (7569993945483394126387688304554631856060004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59344516396189276341/20000000000000000000)
  centralHi := (148361290990473190853/50000000000000000000)
  directionLo := (300601473174601199307/100000000000000000000)
  directionHi := (75150368293650299827/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree040.table
  base := (-262944421239014779443307291249343697143/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-7253455592244430357590223402850000000000000)
      constant := (38164617531989768872450093088817458940709125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree040.table
  base := (-6594569791274994453565851979226529895221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-13364829143919074343899166765450000000000000)
      constant := (72786274828986816133917669668031795742530179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300601473174601199307/100000000000000000000)
  centralHi := (75150368293650299827/25000000000000000000)
  directionLo := (76107736421815851793/25000000000000000000)
  directionHi := (304430945687263407173/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree041.table
  base := (-1333624615247362050802946186083942743179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-7452765621708015580659800566390000000000000)
      constant := (40709769596043021222116228338075513680531725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree041.table
  base := (-1671807704091584526318783490259826985031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-13731302423900505237930324775830000000000000)
      constant := (77592582128102388276750850167496760047737476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76107736421815851793/25000000000000000000)
  centralHi := (304430945687263407173/100000000000000000000)
  directionLo := (30821284157111715087/10000000000000000000)
  directionHi := (308212841571117150871/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree042.table
  base := (-6757607175417166317951461927174268139953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-7652075651171600803729377729930000000000000)
      constant := (43334877304840748520998619854741182537767915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree042.table
  base := (-3387508320885260695670647043421461188779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1566419522653548459106831420690000000000000)
      constant := (9172011009197090801848155388962395432885738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30821284157111715087/10000000000000000000)
  centralHi := (308212841571117150871/100000000000000000000)
  directionLo := (19496805700574429151/6250000000000000000)
  directionHi := (311948891209190866417/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree043.table
  base := (-1710584115821117474993531440645321855817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-7851385680635186026798954893470000000000000)
      constant := (46039545256143144208189860679198039673377740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree043.table
  base := (-3429094818931317290335344297032554277149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-14464248983863367025992640796590000000000000)
      constant := (87652143267655493164139882093976652650270902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19496805700574429151/6250000000000000000)
  centralHi := (311948891209190866417/100000000000000000000)
  directionLo := (315640722569101714883/100000000000000000000)
  directionHi := (78910180642275428721/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree044.table
  base := (-3461277312722250772059325652102970807779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-8050695710098771249868532057010000000000000)
      constant := (48823421324249855397558033597814414365518690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree044.table
  base := (-867122855893959997789207145406828442481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-14830722263844797920023798806970000000000000)
      constant := (92904108539181501113430367438334713768855352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315640722569101714883/100000000000000000000)
  centralHi := (78910180642275428721/25000000000000000000)
  directionLo := (31928986949360869871/10000000000000000000)
  directionHi := (319289869493608698711/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree045.table
  base := (-3499239340533433942872641144649017924099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-8250005739562356472938109220550000000000000)
      constant := (51686191916460800501007586410264338199353890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree045.table
  base := (-7011603266002143338652380803553000253721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1688577282647358757117217424150000000000000)
      constant := (10922606277756423738729866858773182926674631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31928986949360869871/10000000000000000000)
  centralHi := (319289869493608698711/100000000000000000000)
  directionLo := (8072444478693656243/2500000000000000000)
  directionHi := (322897779147746249721/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree046.table
  base := (-3535150952125865467593989352686529264249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-8449315769025941696007686384090000000000000)
      constant := (54627577751701245413605946934587930426320390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree046.table
  base := (-7082234758083612509416560432714187955483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-15563668823807659708086114827730000000000000)
      constant := (103849708920129832746398232878770397127788717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8072444478693656243/2500000000000000000)
  centralHi := (322897779147746249721/100000000000000000000)
  directionLo := (163232909362548389629/50000000000000000000)
  directionHi := (326465818725096779259/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree047.table
  base := (-223068638261822628086365128789784363201/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-8648625798489526919077263547630000000000000)
      constant := (57647330103018197863225131713808371045585760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree047.table
  base := (-714904064127084499204880593965777834171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-15930142103789090602117272838110000000000000)
      constant := (109542441010355314156070432566690118533212290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163232909362548389629/50000000000000000000)
  centralHi := (326465818725096779259/100000000000000000000)
  directionLo := (329995281501340241401/100000000000000000000)
  directionHi := (164997640750670120701/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree048.table
  base := (-3601157770533811822111181117321889276993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-8847935827953112142146840711170000000000000)
      constant := (60745227452459347142966443204827739989490230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree048.table
  base := (-7212165984841994483151336053570080491111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-1810735042641169055127603427610000000000000)
      constant := (12820141716143531123635892208678246738068921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329995281501340241401/100000000000000000000)
  centralHi := (164997640750670120701/50000000000000000000)
  directionLo := (83371848077772116679/25000000000000000000)
  directionHi := (333487392311088466717/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree049.table
  base := (-726279578530592646820888613704181133439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-9047245857416697365216417874710000000000000)
      constant := (63921072512749494237178039790346582621806450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree049.table
  base := (-7271739649572112941484907857931716862603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-16663088663751952390179588858870000000000000)
      constant := (121365877058063320471619295638879604440369597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83371848077772116679/25000000000000000000)
  centralHi := (333487392311088466717/100000000000000000000)
  directionLo := (336943312513768204409/100000000000000000000)
  directionHi := (33694331251376820441/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree050.table
  base := (-7319758754705988505542664416380958398443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-9246555886880282588285995038250000000000000)
      constant := (67174689575338206820045876060829515114249865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree050.table
  base := (-7327876099593165713033030031327860943769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-17029561943733383284210746869250000000000000)
      constant := (127495948127462693367856123776016233685256831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336943312513768204409/100000000000000000000)
  centralHi := (33694331251376820441/10000000000000000000)
  directionLo := (85091036126408426433/25000000000000000000)
  directionHi := (340364144505633705733/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree051.table
  base := (-3686656373873176796553612121279808641429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-555639171549639283020916011870000000000000)
      constant := (4147407185230822885133720897398432530957070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree051.table
  base := (-7380677011613418157529794710324277257877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (352)
      previous := (209)
      next := (0)
      square := (3214677894573955210799631670000000000000)
      linear := (-113699576625587020772822907710000000000000)
      constant := (874321726747527454906961703544487286616091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85091036126408426433/25000000000000000000)
  centralHi := (340364144505633705733/100000000000000000000)
  directionLo := (34375093582760315327/10000000000000000000)
  directionHi := (343750935827603153271/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree052.table
  base := (-74235542190641586225334261517708966407/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-9645175945807453034425149365330000000000000)
      constant := (73914630856556178110453583900379054354188500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree052.table
  base := (-1486046540839304469655064955284778786439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-17762508503696245072273062890010000000000000)
      constant := (140191470334206283127692726622961451882360805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34375093582760315327/10000000000000000000)
  centralHi := (343750935827603153271/100000000000000000000)
  directionLo := (173552341456154070551/50000000000000000000)
  directionHi := (347104682912308141103/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree053.table
  base := (-7470569075431389744737990593238171038211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-9844485975271038257494726528870000000000000)
      constant := (77400691562949254021512200945518842849785105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree053.table
  base := (-7476623407243538917223827030808692704831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-18128981783677675966304220900390000000000000)
      constant := (146756477874993782244925989828106590274734569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173552341456154070551/50000000000000000000)
  centralHi := (347104682912308141103/100000000000000000000)
  directionLo := (70085266901669145973/20000000000000000000)
  directionHi := (175213167254172864933/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree054.table
  base := (-1502886765975573560929157436608243065441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-10043796004734623480564303692410000000000000)
      constant := (80963993706775125659532669795957443852188775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree054.table
  base := (-3759960194778709153069737892023482791689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2055050562628789651148375434530000000000000)
      constant := (17051784604953080428159590319550426946403758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70085266901669145973/20000000000000000000)
  centralHi := (175213167254172864933/50000000000000000000)
  directionLo := (8842919870377093641/2500000000000000000)
  directionHi := (353716794815083745641/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree055.table
  base := (-188880415737540339155483608534679813999/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-10243106034198208703633880855950000000000000)
      constant := (84604438815477153020589136884495506750857800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree055.table
  base := (-378009348018174576665726329446647719847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-18861928343640537754366536921150000000000000)
      constant := (160320056375663021974645539073685385613559060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8842919870377093641/2500000000000000000)
  centralHi := (353716794815083745641/100000000000000000000)
  directionLo := (356976926357372702147/100000000000000000000)
  directionHi := (89244231589343175537/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree056.table
  base := (-1518595634159880990234823471557127171849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-10442416063661793926703458019490000000000000)
      constant := (88321939182617492007802769317791756183390975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree056.table
  base := (-7597479358880690803238096336662898201339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-19228401623621968648397694931530000000000000)
      constant := (167318316390041233944677475387299801778317261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356976926357372702147/100000000000000000000)
  centralHi := (89244231589343175537/25000000000000000000)
  directionLo := (180103776313031628981/50000000000000000000)
  directionHi := (360207552626063257963/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree057.table
  base := (-7627772514832156503544414897456238347433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-10641726093125379149773035183030000000000000)
      constant := (92116416689963121105043991074603735587959315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree057.table
  base := (-152636950889200634481309518882048069537/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2177208322622599949158761437990000000000000)
      constant := (19384523504826707574080023349114405395190350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180103776313031628981/50000000000000000000)
  centralHi := (360207552626063257963/100000000000000000000)
  directionLo := (363409460507234414443/100000000000000000000)
  directionHi := (90852365126808603611/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree058.table
  base := (-1914911953297360236823037601490310587573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-10841036122588964372842612346570000000000000)
      constant := (95987801758467107726187837226094004803828060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree058.table
  base := (-1915833974601554996023396128075632456399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-19961348183584830436460010952290000000000000)
      constant := (181747126400086885145513456756041119923624804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363409460507234414443/100000000000000000000)
  centralHi := (90852365126808603611/25000000000000000000)
  directionLo := (183291701260218139487/50000000000000000000)
  directionHi := (14663336100817451159/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree059.table
  base := (-12013510866431269488943334630430845291/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-11040346152052549595912189510110000000000000)
      constant := (99936032414037782065952544917409554274883200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree059.table
  base := (-1922995961838705289052497912760114687421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-20327821463566261330491168962670000000000000)
      constant := (189177458411301678825976646674303766792071916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183291701260218139487/50000000000000000000)
  centralHi := (14663336100817451159/4000000000000000000)
  directionLo := (18486504944199244559/5000000000000000000)
  directionHi := (369730098883984891181/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree060.table
  base := (-3857404070146940799745988165029200142771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-11239656181516134818981766673650000000000000)
      constant := (103961053455533638924306803467265611587391810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree060.table
  base := (-3858913208486704045135114328612187449897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2299366082616410247169147441450000000000000)
      constant := (21861290719480376913959504777062155653959534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18486504944199244559/5000000000000000000)
  centralHi := (369730098883984891181/100000000000000000000)
  directionLo := (186425119711683626249/50000000000000000000)
  directionHi := (372850239423367252499/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree061.table
  base := (-7738165397621612122665183711809412402247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-11438966210979720042051343837190000000000000)
      constant := (108062815713797253616509909540847399078753085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree061.table
  base := (-7740894723774728330677698268335583897063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-21060768023529123118553484983430000000000000)
      constant := (204469519658102368981496895193619146283739137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186425119711683626249/50000000000000000000)
  centralHi := (372850239423367252499/100000000000000000000)
  directionLo := (375944485337081812339/100000000000000000000)
  directionHi := (18797224266854090617/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree062.table
  base := (-387937451794252447092396450700035746237/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-11638276240443305265120921000730000000000000)
      constant := (112241275391766080262922255579036966933750700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree062.table
  base := (-970152051494911303541845264783249422809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-21427241303510554012584642993810000000000000)
      constant := (212331096057073086352663660664730146010190328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375944485337081812339/100000000000000000000)
  centralHi := (18797224266854090617/5000000000000000000)
  directionLo := (379013470832719031289/100000000000000000000)
  directionHi := (37901347083271903129/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree063.table
  base := (-1944146513364778379173234130743911840139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-11837586269906890488190498164270000000000000)
      constant := (116496393476788357354345654988068189563996580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree063.table
  base := (-1944704010357881310682098439518944296621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2421523842610220545179533444910000000000000)
      constant := (24481809087991568852623357911176100393106124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379013470832719031289/100000000000000000000)
  centralHi := (37901347083271903129/10000000000000000000)
  directionLo := (19102890232237463569/5000000000000000000)
  directionHi := (382057804644749271381/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree064.table
  base := (-7791700499908393327551971981333877115787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-12036896299370475711260075327810000000000000)
      constant := (120828135217243255981671806269884547567687785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree064.table
  base := (-7793715432446911298722439423718621883423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-22160187863473415800646959014570000000000000)
      constant := (228485020108170969301165712741467864481216777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19102890232237463569/5000000000000000000)
  centralHi := (382057804644749271381/100000000000000000000)
  directionLo := (96269517861076629831/25000000000000000000)
  directionHi := (15403122857772260773/4000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree065.table
  base := (-7804113798555918449435066647612342455301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-12236206328834060934329652491350000000000000)
      constant := (125236469656428997686511214255900165152090055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree065.table
  base := (-7805933971737473345988154994028714257529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-22526661143454846694678117024950000000000000)
      constant := (236777260580923638861435198746531314216167071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96269517861076629831/25000000000000000000)
  centralHi := (15403122857772260773/4000000000000000000)
  directionLo := (12127338535944229337/3125000000000000000)
  directionHi := (77614966630043067757/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree066.table
  base := (-7813845033756686956391551500771885670699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-12435516358297646157399229654890000000000000)
      constant := (129721369217452610251862595681516625205839945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree066.table
  base := (-1953872221105318549202776390171235509107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2543681602604030843189919448370000000000000)
      constant := (27245884267516671886629324934702051751472308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12127338535944229337/3125000000000000000)
  centralHi := (77614966630043067757/20000000000000000000)
  directionLo := (12220269692174594919/3125000000000000000)
  directionHi := (391048630149587037409/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree067.table
  base := (-977613900842248661087067373661208829713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-12634826387761231380468806818430000000000000)
      constant := (134282809333540658991528413058684425928517720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree067.table
  base := (-977799434440036503508808199975871467667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-23259607703417708482740433045710000000000000)
      constant := (253792073779988028417789156926442066500785064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12220269692174594919/3125000000000000000)
  centralHi := (391048630149587037409/100000000000000000000)
  directionLo := (196999991217746980749/50000000000000000000)
  directionHi := (393999982435493961499/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree068.table
  base := (-7825327463445999714865590015154894321207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-754949201013224506090493175410000000000000)
      constant := (8171809889341230711029628287295833982697405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree068.table
  base := (-3913333672241817630501353436687204460967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3168)
      previous := (1881)
      next := (0)
      square := (28932101051165596897196685030000000000000)
      linear := (-1389769469611714080986564179770000000000000)
      constant := (15442033607398261892480872543293715434944098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196999991217746980749/50000000000000000000)
  centralHi := (393999982435493961499/100000000000000000000)
  directionLo := (198464695334252452173/50000000000000000000)
  directionHi := (396929390668504904347/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree069.table
  base := (-3913553648730881652942766289665724557601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-13033446446688401826607961145510000000000000)
      constant := (143635226075008789412212432696158056028533110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree069.table
  base := (-391415828786669034758707532656954475031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2665839362597841141200305451830000000000000)
      constant := (30153379957046166276349883523682803134320820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198464695334252452173/50000000000000000000)
  centralHi := (396929390668504904347/100000000000000000000)
  directionLo := (99959334292054619723/25000000000000000000)
  directionHi := (399837337168218478893/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree070.table
  base := (-1565252546142909338826808565341550078141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-13232756476151987049677538309050000000000000)
      constant := (148426165830476470681868926465707300685431275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree070.table
  base := (-3913676953956543523837284138444547929341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-24359027543362001164833907076850000000000000)
      constant := (280389590711711265139561017108311461671568118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99959334292054619723/25000000000000000000)
  centralHi := (399837337168218478893/100000000000000000000)
  directionLo := (402724286840355165039/100000000000000000000)
  directionHi := (5034053585504439563/1250000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree071.table
  base := (-7822804474422032943137578517589730134703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-13432066505615572272747115472590000000000000)
      constant := (153293571907494413869677430729034839955354165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree071.table
  base := (-312951555368779694647333593242369277143/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-24725500823343432058865065087230000000000000)
      constant := (289542059798803042467396961816674937753776425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402724286840355165039/100000000000000000000)
  centralHi := (5034053585504439563/1250000000000000000)
  directionLo := (101397672011113531291/25000000000000000000)
  directionHi := (81118137608890825033/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree072.table
  base := (-7816742072421011755540786912636140147747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-13631376535079157495816692636130000000000000)
      constant := (158237430515218457855316430194488777486505585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree072.table
  base := (-7817629985931837407414608174561420500533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2787997122591651439210691455290000000000000)
      constant := (33204200534987058140271477806911749475345963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101397672011113531291/25000000000000000000)
  centralHi := (81118137608890825033/20000000000000000000)
  directionLo := (408436973406760446879/100000000000000000000)
  directionHi := (2552731083792252793/625000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree073.table
  base := (-61000656475120877046723810119169666609/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-13830686564542742718886269799670000000000000)
      constant := (163257729365218338345015489219546378463999360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree073.table
  base := (-7808884751016926501421460894105847648731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-25458447383306293846927381107990000000000000)
      constant := (308276806153701049462231951631870690265650669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408436973406760446879/100000000000000000000)
  centralHi := (2552731083792252793/625000000000000000)
  directionLo := (411263560582475843723/100000000000000000000)
  directionHi := (102815890145618960931/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree074.table
  base := (-62374703373265314650478700216861402617/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-14029996594006327941955846963210000000000000)
      constant := (168354457507207831778282490028101409152304375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree074.table
  base := (-1949389969869529858588106668751306381129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-25824920663287724740958539118370000000000000)
      constant := (317859046388546882262990592815171408410733884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411263560582475843723/100000000000000000000)
  centralHi := (102815890145618960931/25000000000000000000)
  directionLo := (414070852971175473691/100000000000000000000)
  directionHi := (103517713242793868423/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree075.table
  base := (-3891505252096960823597299966250084138243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-14229306623469913165025424126750000000000000)
      constant := (173527605182748153482219710727537256840477730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree075.table
  base := (-3891830663464995356898085503753330263587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-2910154882585461737221077458750000000000000)
      constant := (36398278892096390374497900541330575107646714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414070852971175473691/100000000000000000000)
  centralHi := (103517713242793868423/25000000000000000000)
  directionLo := (83371848077772116679/20000000000000000000)
  directionHi := (104214810097215145849/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree076.table
  base := (-1941651948756452948526944642968333759741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-14428616652933498388095001290290000000000000)
      constant := (178777163694957870797263892228515030868697020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree076.table
  base := (-7767194387714774373405802047621131982717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-26557867223250586529020855139130000000000000)
      constant := (337453183304078792063171753488497435712953083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83371848077772116679/20000000000000000000)
  centralHi := (104214810097215145849/25000000000000000000)
  directionLo := (419629099699816924807/100000000000000000000)
  directionHi := (52453637462477115601/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree077.table
  base := (-1549527031683249510652860428344667632537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-14627926682397083611164578453830000000000000)
      constant := (184103125292477797254559462564597776354920175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree077.table
  base := (-1549632753745920876383734772765446913643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-26924340503232017423052013149510000000000000)
      constant := (347465053971541272888376680732625362888072785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419629099699816924807/100000000000000000000)
  centralHi := (52453637462477115601/12500000000000000000)
  directionLo := (105595198852794655243/25000000000000000000)
  directionHi := (422380795411178620973/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree078.table
  base := (-1545219475160511545563518117088648010159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-14827236711860668834234155617370000000000000)
      constant := (189505483066130992733549729917582518126601225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree078.table
  base := (-48291085343768088477708407945776245881/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3032312642579272035231463462210000000000000)
      constant := (39735567905110672505358059458447306390462560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105595198852794655243/25000000000000000000)
  centralHi := (422380795411178620973/100000000000000000000)
  directionLo := (85022936046570626261/20000000000000000000)
  directionHi := (212557340116426565653/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree079.table
  base := (-1925499677372098077783262497277568959723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-15026546741324254057303732780910000000000000)
      constant := (194984230856888682993821682493087651412801060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree079.table
  base := (-3851213883971068108159622317107593333939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-27657287063194879211114329170270000000000000)
      constant := (367918345148062242999829433493666299476849322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85022936046570626261/20000000000000000000)
  centralHi := (212557340116426565653/50000000000000000000)
  directionLo := (427831095605242334657/100000000000000000000)
  directionHi := (213915547802621167329/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree080.table
  base := (-3837671479683568969956971835630901228679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-15225856770787839280373309944450000000000000)
      constant := (200539363173904924345339104795826695449117690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree080.table
  base := (-3837864708536156278612162140590426662657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-28023760343176310105145487180650000000000000)
      constant := (378359747369665366072517051828648600500858286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427831095605242334657/100000000000000000000)
  centralHi := (213915547802621167329/50000000000000000000)
  directionLo := (430530372196994999627/100000000000000000000)
  directionHi := (107632593049248749907/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree081.table
  base := (-764613351343983129371959817471150503489/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-15425166800251424503442887107990000000000000)
      constant := (206170875121518218786138769971433875224583950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree081.table
  base := (-7646481545992538162115622054140923272161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3154470402573082333241849465670000000000000)
      constant := (43216034461611569299509791633793273174345471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430530372196994999627/100000000000000000000)
  centralHi := (107632593049248749907/25000000000000000000)
  directionLo := (1353790094921390107/312500000000000000)
  directionHi := (433212830374844834241/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree082.table
  base := (-7614373392806621067886723925432949920571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-15624476829715009726512464271530000000000000)
      constant := (211878762334238851451459131454377387364774905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree082.table
  base := (-3807343386598613243980347469573438812407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-28756706903139171893207803201410000000000000)
      constant := (399672026691874546467470036399418971297858786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1353790094921390107/312500000000000000)
  centralHi := (433212830374844834241/100000000000000000000)
  directionLo := (435878780647423947419/100000000000000000000)
  directionHi := (21793939032371197371/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree083.table
  base := (-7580065291736521783217305796801211093569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-15823786859178594949582041435070000000000000)
      constant := (217663020918848096358741321102630249969792795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree083.table
  base := (-7580347428335822961594752845985639344817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-29123180183120602787238961211790000000000000)
      constant := (410542890922358426832964405939131352064130983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435878780647423947419/100000000000000000000)
  centralHi := (21793939032371197371/5000000000000000000)
  directionLo := (438528524084792184649/100000000000000000000)
  directionHi := (8770570481695843693/2000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree084.table
  base := (-7543211613354026127515013038258879093927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-16023096888642180172651618598610000000000000)
      constant := (223523647402831061574109036850747919709275485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree084.table
  base := (-471466599026311530949308052050472175253/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3276628162566892631252235469130000000000000)
      constant := (46839655272672204907057124026558616661630128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438528524084792184649/100000000000000000000)
  centralHi := (8770570481695843693/2000000000000000000)
  directionLo := (220581176357643444561/50000000000000000000)
  directionHi := (441162352715286889123/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree085.table
  base := (-7503814501422207152232090901646265089969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-954259230476809729160070338950000000000000)
      constant := (13497684628732359208130222606460067467352635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree085.table
  base := (-1876010771609521834023591766264054469319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3168)
      previous := (1881)
      next := (0)
      square := (28932101051165596897196685030000000000000)
      linear := (-1756242749593144975017722190150000000000000)
      constant := (25453767146361284402338755372046398664776772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220581176357643444561/50000000000000000000)
  centralHi := (441162352715286889123/100000000000000000000)
  directionLo := (443780549901173829367/100000000000000000000)
  directionHi := (55472568737646728671/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree086.table
  base := (-1865468967162363798936871012661671312173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-16421716947569350618790772925690000000000000)
      constant := (235473992011841607212097988440827539815640060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree086.table
  base := (-7462081576758320593415627171668181046201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-30222600023064895469332435242930000000000000)
      constant := (444014318752826935988917621601551061098831199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443780549901173829367/100000000000000000000)
  centralHi := (55472568737646728671/12500000000000000000)
  directionLo := (89276678138893423627/20000000000000000000)
  directionHi := (55797923836808389767/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree087.table
  base := (-231793669434382852280331510618085458191/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-16621026977032935841860350089230000000000000)
      constant := (241563704906586388529217543333987728413248160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree087.table
  base := (-7417582517712656511266413612164022479473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3398785922560702929262621472590000000000000)
      constant := (50606413938286920978227856863344597503432303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89276678138893423627/20000000000000000000)
  centralHi := (55797923836808389767/12500000000000000000)
  directionLo := (89794228434836570273/20000000000000000000)
  directionHi := (224485571087091425683/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree088.table
  base := (-3685190342324375226704816861695488031109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-16820337006496521064929927252770000000000000)
      constant := (247729775171264296414133143405268039590094990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree088.table
  base := (-1842636802911012133545122363860630491701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-30955546583027757257394751263690000000000000)
      constant := (467044258176013871375925794088234000364342796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89794228434836570273/20000000000000000000)
  centralHi := (224485571087091425683/50000000000000000000)
  directionLo := (451544063766196963477/100000000000000000000)
  directionHi := (225772031883098481739/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree089.table
  base := (-7320827016976875790984218421272615191827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-17019647035960106287999504416310000000000000)
      constant := (253972200840556952053930882527073071047809985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree089.table
  base := (-3660488409359866330566981851113661061267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-31322019863009188151425909274070000000000000)
      constant := (478773913929526702871206009045066735159289066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451544063766196963477/100000000000000000000)
  centralHi := (225772031883098481739/50000000000000000000)
  directionLo := (454102407546791572329/100000000000000000000)
  directionHi := (45410240754679157233/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree090.table
  base := (-363436881669280362118105574989860457477/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-17218957065423691511069081579850000000000000)
      constant := (260290980159510439411225863298493032778914700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree090.table
  base := (-7268872372753997520200899890720885724989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3520943682554513227273007476050000000000000)
      constant := (54516298890685535396474524153081664025478179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454102407546791572329/100000000000000000000)
  centralHi := (45410240754679157233/10000000000000000000)
  directionLo := (456646418530895110759/100000000000000000000)
  directionHi := (11416160463272377769/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree091.table
  base := (-7214113618658746821358404915530265402591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-17418267094887276734138658743390000000000000)
      constant := (266686111560612164576055277842290766493256005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree091.table
  base := (-1803558698815950197823799438568821941203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-32054966422972049939488225294830000000000000)
      constant := (502662584039077611541663865879789976523723988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456646418530895110759/100000000000000000000)
  centralHi := (11416160463272377769/2500000000000000000)
  directionLo := (91835266989189825879/20000000000000000000)
  directionHi := (114794083736487282349/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree092.table
  base := (-3578477970996127827736346944380023026413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-17617577124350861957208235906930000000000000)
      constant := (273157593643373963719182211065149733453666430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree092.table
  base := (-7157064907954750369363197612547740346799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-32421439702953480833519383305210000000000000)
      constant := (514821593860993795656630023379803327357975801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91835266989189825879/20000000000000000000)
  centralHi := (114794083736487282349/25000000000000000000)
  directionLo := (230846194246134097779/50000000000000000000)
  directionHi := (461692388492268195559/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree093.table
  base := (-44357909184868366002417623845435005029/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-17816887153814447180277813070470000000000000)
      constant := (279705425156147233881946402150163426837295200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree093.table
  base := (-7097363443812888303593223738150328112247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3643101442548323525283393479510000000000000)
      constant := (58569301952824630615914484271634555175560617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230846194246134097779/50000000000000000000)
  centralHi := (461692388492268195559/100000000000000000000)
  directionLo := (232097402295349128597/50000000000000000000)
  directionHi := (92838960918139651439/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree094.table
  base := (-175876074395437091840157747888022637211/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-18016197183278032403347390234010000000000000)
      constant := (286329604979925870705652364263764291569204200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree094.table
  base := (-1758782764239525865166028062127892553893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-33154386262916342621581699325970000000000000)
      constant := (539568953480995420259233218333081405869297228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232097402295349128597/50000000000000000000)
  centralHi := (92838960918139651439/20000000000000000000)
  directionLo := (233341901309161348111/50000000000000000000)
  directionHi := (466683802618322696223/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree095.table
  base := (-1742572288324092335175409259201339126701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-18215507212741617626416967397550000000000000)
      constant := (293030132113919522980950764141616259847668220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree095.table
  base := (-6970368331397579147528030501926053452309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-33520859542897773515612857336350000000000000)
      constant := (552157300058712346023256015745990334970544291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233341901309161348111/50000000000000000000)
  centralHi := (466683802618322696223/100000000000000000000)
  directionLo := (234579798066456809667/50000000000000000000)
  directionHi := (93831919226582723867/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree096.table
  base := (-6903004621686679131806831330062448372161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-18414817242205202849486544561090000000000000)
      constant := (299807005662703474948997928215611762102227355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree096.table
  base := (-862884473600276191606208481730835768811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3765259202542133823293779482970000000000000)
      constant := (62765417327967384122511321518878307702508968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234579798066456809667/50000000000000000000)
  centralHi := (93831919226582723867/20000000000000000000)
  directionLo := (2947639956792364547/625000000000000000)
  directionHi := (471622393086778327521/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree097.table
  base := (-854148741957899637269446583157262464369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-18614127271668788072556121724630000000000000)
      constant := (306660224824772663655761189073650045911894360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree097.table
  base := (-683325389541517595646098698162191018003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-34253806102860635303675173357110000000000000)
      constant := (577763319947279238832367917181041411621741970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2947639956792364547/625000000000000000)
  centralHi := (471622393086778327521/100000000000000000000)
  directionLo := (9481447920612140177/2000000000000000000)
  directionHi := (474072396030607008851/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree098.table
  base := (-845105698995011488573996558526720689741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-18813437301132373295625698888170000000000000)
      constant := (313589788882346215374760805705419108826594040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree098.table
  base := (-1690225767047416943012945004849485328629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-34620279382842066197706331367490000000000000)
      constant := (590780990960935445703606936938485954640943884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9481447920612140177/2000000000000000000)
  centralHi := (474072396030607008851/100000000000000000000)
  directionLo := (19060392092315487521/4000000000000000000)
  directionHi := (238254901153943594013/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree099.table
  base := (-6685972035655864666996352774273702848547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-19012747330595958518695276051710000000000000)
      constant := (320595697192285696010889712769846499383849585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree099.table
  base := (-6686023680241890498418775088349510919377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-3887416962535944121304165486430000000000000)
      constant := (67104640891355536351325407011006991344300047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19060392092315487521/4000000000000000000)
  centralHi := (238254901153943594013/50000000000000000000)
  directionLo := (95786960848082609613/20000000000000000000)
  directionHi := (239467402120206524033/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree100.table
  base := (-1321713933154374911528555844932829539601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-19212057360059543741764853215250000000000000)
      constant := (327677949178005241542871885415360306576382775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree100.table
  base := (-6608616065695874222129273455612551016471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-35353225942804927985768647388250000000000000)
      constant := (617245650262015780952171545066951754806158929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95786960848082609613/20000000000000000000)
  centralHi := (239467402120206524033/50000000000000000000)
  directionLo := (120336897326345787289/25000000000000000000)
  directionHi := (481347589305383149157/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree101.table
  base := (-261145553610381186775564793091012076317/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-19411367389523128964834430378790000000000000)
      constant := (334836544322265067282307704370559188743048375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree101.table
  base := (-6528680523988041912080658624477407587449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-35719699222786358879799805398630000000000000)
      constant := (630692636901549170932233488350094262865045151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120336897326345787289/25000000000000000000)
  centralHi := (481347589305383149157/100000000000000000000)
  directionLo := (48374834030454806749/10000000000000000000)
  directionHi := (483748340304548067491/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree102.table
  base := (-6446179880443013329490765590233346414537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-1153569259940394952229647502490000000000000)
      constant := (20121851891808925195371360566394165554764355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree102.table
  base := (-402888582730743764419669369415041069387/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (352)
      previous := (209)
      next := (0)
      square := (3214677894573955210799631670000000000000)
      linear := (-235857336619397318783208911170000000000000)
      constant := (4210998217269544485445120424499108829126736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48374834030454806749/10000000000000000000)
  centralHi := (483748340304548067491/100000000000000000000)
  directionLo := (486137235525839845487/100000000000000000000)
  directionHi := (30383577220364990343/6250000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree103.table
  base := (-3180596537488549264738751789817156465917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-19809987448450299410973584705870000000000000)
      constant := (349382762276359077687127618879276417813499870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree103.table
  base := (-636122670591646766563068720275764457561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-36452645782749220667862121419390000000000000)
      constant := (658015920656964629888535679891367366458838390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486137235525839845487/100000000000000000000)
  centralHi := (30383577220364990343/6250000000000000000)
  directionLo := (61064306112235960881/12500000000000000000)
  directionHi := (488514448897887687049/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree104.table
  base := (-6273678683373086136603946820683134651601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-20009297477913884634043161869410000000000000)
      constant := (356770384294093285626568256300864870428436555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree104.table
  base := (-6273708887326061415111075832343379003099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-36819119062730651561893279429770000000000000)
      constant := (671892216582178252745797508831834871212939501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61064306112235960881/12500000000000000000)
  centralHi := (488514448897887687049/100000000000000000000)
  directionLo := (490880150137798868479/100000000000000000000)
  directionHi := (191750058647577683/39062500000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree105.table
  base := (-6183636939140098911475829964600810722073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-20208607507377469857112739032950000000000000)
      constant := (364234347876533669750559755322451828506604515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree105.table
  base := (-772958007852967638800252519057048408199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4131732482523564717324937493350000000000000)
      constant := (76212401612326479638224187811940104080243912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490880150137798868479/100000000000000000000)
  centralHi := (191750058647577683/39062500000000000)
  directionLo := (123308626223140051183/25000000000000000000)
  directionHi := (493234504892560204733/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree106.table
  base := (-6091068052583794842808088087504147346217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-20407917536841055080182316196490000000000000)
      constant := (371774652719788554265409034759048507084716435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree106.table
  base := (-1522773101983994810449408024570041497007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-37552065622693513349955595450530000000000000)
      constant := (700074113986700466935941239174833288265139172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123308626223140051183/25000000000000000000)
  centralHi := (493234504892560204733/100000000000000000000)
  directionLo := (99115534974878692747/20000000000000000000)
  directionHi := (61947209359299182967/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree107.table
  base := (-2997986106649980226176695934400143879449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-20607227566304640303251893360030000000000000)
      constant := (379391298549892027647183485478911584188392390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree107.table
  base := (-2997997040465964271453844005485428227001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-37918538902674944243986753460910000000000000)
      constant := (714379714597806637061449127170604802363140798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99115534974878692747/20000000000000000000)
  centralHi := (61947209359299182967/12500000000000000000)
  directionLo := (31119363624398607753/6250000000000000000)
  directionHi := (497909817990377724049/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree108.table
  base := (-2949174796198172806012322666400186483959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-20806537595768225526321470523570000000000000)
      constant := (387084285119593391330968961166911461061358490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree108.table
  base := (-5898369224706926483316850117342003792693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4253890242517375015335323496810000000000000)
      constant := (80980935108065117151350183093648160903911723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31119363624398607753/6250000000000000000)
  centralHi := (497909817990377724049/100000000000000000000)
  directionLo := (250115544233316350037/50000000000000000000)
  directionHi := (20009243538665308003/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree109.table
  base := (-5798200344472450920648219257966193352081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-21005847625231810749391047687110000000000000)
      constant := (394853612205496366951461356048170850606242955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree109.table
  base := (-1449554492114140983848148445833161271571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-38651485462637806032049069481670000000000000)
      constant := (743420217775000986979020997764711790130575316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250115544233316350037/50000000000000000000)
  centralHi := (20009243538665308003/4000000000000000000)
  directionLo := (502541636967339402553/100000000000000000000)
  directionHi := (251270818483669701277/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree110.table
  base := (-227820984375349108490005797866773653663/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-21205157654695395972460624850650000000000000)
      constant := (402699279605509827330993054890762801761424125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree110.table
  base := (-2847770214582351197493520912476782922589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-39017958742619236926080227492050000000000000)
      constant := (758155119700776411161345805491795775236692022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502541636967339402553/100000000000000000000)
  centralHi := (251270818483669701277/50000000000000000000)
  directionLo := (252420805354429028913/50000000000000000000)
  directionHi := (504841610708858057827/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree111.table
  base := (-1118064502762751117370851187962988100707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-21404467684158981195530202014190000000000000)
      constant := (410621287136575999947529618228079410972391925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree111.table
  base := (-5590336712926210438581266633606405583409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4376048002511185313345709500270000000000000)
      constant := (85892569052662174860188755748227748786394799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252420805354429028913/50000000000000000000)
  centralHi := (504841610708858057827/100000000000000000000)
  directionLo := (507131153569187883819/100000000000000000000)
  directionHi := (25356557678459394191/5000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree112.table
  base := (-1370648543168846007263463486281349529427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-21603777713622566418599779177730000000000000)
      constant := (418619634632645817295833725092461799719911940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree112.table
  base := (-5482606916122868610565699245375996853149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-39750905302582098714142543512810000000000000)
      constant := (788054222843861463524120475366617032184959451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507131153569187883819/100000000000000000000)
  centralHi := (25356557678459394191/5000000000000000000)
  directionLo := (254705203096499514253/50000000000000000000)
  directionHi := (509410406192999028507/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree113.table
  base := (-5372339690359528531068006800718005278053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-21803087743086151641669356341270000000000000)
      constant := (426694321942874406489648822457830482373213415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree113.table
  base := (-5372351126468829985016420267753756002787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-40117378582563529608173701523190000000000000)
      constant := (803218423582337568362938940729412480636751013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254705203096499514253/50000000000000000000)
  centralHi := (509410406192999028507/100000000000000000000)
  directionLo := (255839753046226819679/50000000000000000000)
  directionHi := (511679506092453639359/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree114.table
  base := (-262977958092413339136086933969222564357/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-22002397772549736864738933504810000000000000)
      constant := (434845348930012665267177750394501467890082700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree114.table
  base := (-5259569423940192219843467618902385219047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4498205762504995611356095503730000000000000)
      constant := (90947302609041117583325576577477210671695417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255839753046226819679/50000000000000000000)
  centralHi := (511679506092453639359/100000000000000000000)
  directionLo := (256969293872010289211/50000000000000000000)
  directionHi := (513938587744020578423/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree115.table
  base := (-2572126336853529713827499416921309642481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-22201707802013322087808510668350000000000000)
      constant := (443072715468973502998360782232297415133229910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree115.table
  base := (-5144261881601610244688416532687550064131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-40850325142526391396236017543950000000000000)
      constant := (833976122350917765713096483586979682283195269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256969293872010289211/50000000000000000000)
  centralHi := (513938587744020578423/100000000000000000000)
  directionLo := (516187782681476661431/100000000000000000000)
  directionHi := (64523472835184582679/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree116.table
  base := (-2513210152484649059957522257531517211609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-22401017831476907310878087831890000000000000)
      constant := (451376421445553668743099631243565915258449990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree116.table
  base := (-62830357079267923823265250101821078843/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-41216798422507822290267175554330000000000000)
      constant := (849569620017004092802185636147973069914348560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516187782681476661431/100000000000000000000)
  centralHi := (64523472835184582679/12500000000000000000)
  directionLo := (32401701224079776271/6250000000000000000)
  directionHi := (518427219585276420337/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree117.table
  base := (-4906062127924939335344521048989616881471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-22600327860940492533947664995430000000000000)
      constant := (459756466755294175393801674932318003606274405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree117.table
  base := (-153314673110174112485784181021703172571/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4620363522498805909366481507190000000000000)
      constant := (96145135146668479086525011413471289060063392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32401701224079776271/6250000000000000000)
  centralHi := (518427219585276420337/100000000000000000000)
  directionLo := (520657024368462211653/100000000000000000000)
  directionHi := (260328512184231105827/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree118.table
  base := (-956635641764739234489882677278595024259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-22799637890404077757017242158970000000000000)
      constant := (468212851302464187523125765044690150949728725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree118.table
  base := (-478318485757914109913437110044479802043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-41949744982470684078329491575090000000000000)
      constant := (881185911113192691314116222616883080348861570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520657024368462211653/100000000000000000000)
  centralHi := (260328512184231105827/50000000000000000000)
  directionLo := (522877320259276966997/100000000000000000000)
  directionHi := (261438660129638483499/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree119.table
  base := (-931553721700422983673409400421089044061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-1352879289403980175299224666030000000000000)
      constant := (28043857352891464455656380368797037156274075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree119.table
  base := (-1164443643125989095908601651008540153447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3168)
      previous := (1881)
      next := (0)
      square := (28932101051165596897196685030000000000000)
      linear := (-2489189309556006763080038210910000000000000)
      constant := (52776982603604500779350945195962773426090436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522877320259276966997/100000000000000000000)
  centralHi := (261438660129638483499/50000000000000000000)
  directionLo := (525088227880632960407/100000000000000000000)
  directionHi := (65636028485079120051/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree120.table
  base := (-4529833382942843051088652031863155228577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-23198257949331248203156396486050000000000000)
      constant := (485354637764471374457202451060757740694706235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree120.table
  base := (-2264919366169500027266640863611090087849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4742521282492616207376867510650000000000000)
      constant := (101486066182146487092978237786832789929223278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525088227880632960407/100000000000000000000)
  centralHi := (65636028485079120051/12500000000000000000)
  directionLo := (527289865326581606463/100000000000000000000)
  directionHi := (8238904145727837601/1562500000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree121.table
  base := (-439937258377348687930431030644256862393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-23397567978794833426225973649590000000000000)
      constant := (494040039523811732540200551172842488338421150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree121.table
  base := (-2199688690785116117143830976512028562893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-43049164822414976760422965606230000000000000)
      constant := (929683585131610320799120650945944427415830614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527289865326581606463/100000000000000000000)
  centralHi := (8238904145727837601/1562500000000000000)
  directionLo := (529482348235921464071/100000000000000000000)
  directionHi := (66185293529490183009/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree122.table
  base := (-2133193129355823983906844633406115943321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-23596878008258418649295550813130000000000000)
      constant := (502801780208224035734017247153604324923802310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree122.table
  base := (-106659764037384435778763890566871571131/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-43415638102396407654454123616610000000000000)
      constant := (946135672630736942689949526229162681739530760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529482348235921464071/100000000000000000000)
  centralHi := (66185293529490183009/12500000000000000000)
  directionLo := (531665789863074266617/100000000000000000000)
  directionHi := (265832894931537133309/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree123.table
  base := (-516359306495250872290708082715722133589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-23796188037722003872365127976670000000000000)
      constant := (511639859753832520482483213546094252135711160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree123.table
  base := (-2065439155274350374851508038533645423931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4864679042486426505387253514110000000000000)
      constant := (106970095337414525108030605132387552944967882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531665789863074266617/100000000000000000000)
  centralHi := (265832894931537133309/50000000000000000000)
  directionLo := (2669201505731759481/500000000000000000)
  directionHi := (533840301146351896201/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree124.table
  base := (-1996418602285340941264122651084864684203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-23995498067185589095434705140210000000000000)
      constant := (520554278101325546316509277618436741062653330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree124.table
  base := (-1996420332295112578735361215351895205613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-44148584662359269442516439637370000000000000)
      constant := (979469141256319750907564119456099441140401174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2669201505731759481/500000000000000000)
  centralHi := (533840301146351896201/100000000000000000000)
  directionLo := (536005990773730736781/100000000000000000000)
  directionHi := (268002995386865368391/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree125.table
  base := (-770454910948303209396709086918904884053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-24194808096649174318504282303750000000000000)
      constant := (529545035195498559571413184284510912212717075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree125.table
  base := (-1926138828581672205036353589836467231237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-44515057942340700336547597647750000000000000)
      constant := (996350522202257650337450442500670697463105126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536005990773730736781/100000000000000000000)
  centralHi := (268002995386865368391/50000000000000000000)
  directionLo := (269081482623121874767/50000000000000000000)
  directionHi := (107632593049248749907/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree126.table
  base := (-3709186538118442762657006164128883945253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-24394118126112759541573859467290000000000000)
      constant := (538612130984846076641749871147405762699109415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree126.table
  base := (-3709189319724344695664540384544925564901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-4986836802480236803397639517570000000000000)
      constant := (112597222310302958209615753066406516511743611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269081482623121874767/50000000000000000000)
  centralHi := (107632593049248749907/20000000000000000000)
  directionLo := (16884729029346715217/3125000000000000000)
  directionHi := (108062265787818977389/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree127.table
  base := (-1781786594018809775904643667783054752649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-24593428155576344764643436630830000000000000)
      constant := (547755565421197349907852684731394971764844390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree127.table
  base := (-222723480115434741953748266156769199699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-45248004502303562124609913668510000000000000)
      constant := (1030542576950805400196745360442559892985326416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16884729029346715217/3125000000000000000)
  centralHi := (108062265787818977389/20000000000000000000)
  directionLo := (54245118416059507567/10000000000000000000)
  directionHi := (542451184160595075671/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree128.table
  base := (-17077172678763109683710664235079583359/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-24792738185039929987713013794370000000000000)
      constant := (556975338459390962739995605103710000409249000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree128.table
  base := (-1707718385702352405379066277207067832059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-45614477782284993018641071678890000000000000)
      constant := (1047853250603994935869049554548208833137629082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54245118416059507567/10000000000000000000)
  centralHi := (542451184160595075671/100000000000000000000)
  directionLo := (136145657802253482293/25000000000000000000)
  directionHi := (544582631209013929173/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree129.table
  base := (-652954122127125374151861505545544889397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-24992048214503515210782590957910000000000000)
      constant := (566271450056984119440654692086085438174106675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree129.table
  base := (-816193153683383491512704389507509875219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5108994562474047101408025521030000000000000)
      constant := (118367446853755049398453755308369318584246836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136145657802253482293/25000000000000000000)
  centralHi := (544582631209013929173/100000000000000000000)
  directionLo := (54670576842743657851/10000000000000000000)
  directionHi := (546705768427436578511/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree130.table
  base := (-3111581440357195878038182222655403528829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-25191358243967100433852168121450000000000000)
      constant := (575643900173992858607393644807562941900842095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree130.table
  base := (-388947904597109175666176677625758223263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-46347424342247854806703387699650000000000000)
      constant := (1082903890125329064740482294743463222890343496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54670576842743657851/10000000000000000000)
  centralHi := (546705768427436578511/100000000000000000000)
  directionLo := (274410346128355257071/50000000000000000000)
  directionHi := (548820692256710514143/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree131.table
  base := (-369483381380872852662994490799757517491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-25390668273430685656921745284990000000000000)
      constant := (585092688772659830408574550720946803097804040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree131.table
  base := (-1477934330607555235127588555385888204543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-46713897622229285700734545710030000000000000)
      constant := (1100643855867003108856584116080342609559967314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274410346128355257071/50000000000000000000)
  centralHi := (548820692256710514143/100000000000000000000)
  directionLo := (550927497286563094777/100000000000000000000)
  directionHi := (275463748643281547389/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree132.table
  base := (-349703433429679660106218357651770597623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-25589978302894270879991322448530000000000000)
      constant := (594617815817246645200673853995073531891478120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree132.table
  base := (-55952578211623687039049352225325708371/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5231152322467857399418411524490000000000000)
      constant := (124280768761134378010919422674304043514039050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550927497286563094777/100000000000000000000)
  centralHi := (275463748643281547389/50000000000000000000)
  directionLo := (553026276304966384751/100000000000000000000)
  directionHi := (34564142269060399047/6250000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree133.table
  base := (-659215678248087092920318616065391513389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-25789288332357856103060899612070000000000000)
      constant := (604219281273848127712508290043250037052611580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree133.table
  base := (-2636864006363840274709482867454040553321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-47446844182192147488796861730790000000000000)
      constant := (1136553079019055718137180755853792040520812079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553026276304966384751/100000000000000000000)
  centralHi := (34564142269060399047/6250000000000000000)
  directionLo := (111023424069164442661/20000000000000000000)
  directionHi := (277558560172911106653/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree134.table
  base := (-2473572810021872407227743181370846721239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-25988598361821441326130476775610000000000000)
      constant := (613897085110226102071172658441251126487809645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree134.table
  base := (-123678698454995344339875738725816125211/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-47813317462173578382828019741170000000000000)
      constant := (1154722336320125765659148341216143045166523780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111023424069164442661/20000000000000000000)
  centralHi := (277558560172911106653/50000000000000000000)
  directionLo := (111440023747007358639/20000000000000000000)
  directionHi := (139300029683759198299/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree135.table
  base := (-230775777978550843071694553101056849941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-26187908391285026549200053939150000000000000)
      constant := (623651227295660592159202798999889728518352550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree135.table
  base := (-2307758818456808483790777209062998935483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5353310082461667697428797527950000000000000)
      constant := (130337187855807174896821003318080793307645413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111440023747007358639/20000000000000000000)
  centralHi := (139300029683759198299/25000000000000000000)
  directionLo := (559275359135050878747/100000000000000000000)
  directionHi := (139818839783762719687/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree136.table
  base := (-1069708821292162933952105352652935453903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-1552189318867565398368801829570000000000000)
      constant := (37263629870636267803316603590385000972836490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree136.table
  base := (-1069709286653194347052160080313491362073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3168)
      previous := (1881)
      next := (0)
      square := (28932101051165596897196685030000000000000)
      linear := (-2855662589537437657111196221290000000000000)
      constant := (70087655418610969299787957457104071643205662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559275359135050878747/100000000000000000000)
  centralHi := (139818839783762719687/25000000000000000000)
  directionLo := (140335731896972068093/25000000000000000000)
  directionHi := (561342927587888272373/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree137.table
  base := (-30758631528806347815472939303778666833/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-26586528450212196995339208266230000000000000)
      constant := (643388526597624451735386990552054548891284160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree137.table
  base := (-1968553251791002341019096204400155200687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-48912737302117871064921493772310000000000000)
      constant := (1210088690515303212838813324292195196323013113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140335731896972068093/25000000000000000000)
  centralHi := (561342927587888272373/100000000000000000000)
  directionLo := (563402908556782491991/100000000000000000000)
  directionHi := (70425363569597811499/12500000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree138.table
  base := (-1795162124186934303129065063983503333527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-26785838479675782218408785429770000000000000)
      constant := (653371683659173209511141533694211837683053485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree138.table
  base := (-897581435691362837176249008821777629767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5475467842455477995439183531410000000000000)
      constant := (136536703983729989774763126008161012529994674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563402908556782491991/100000000000000000000)
  centralHi := (70425363569597811499/12500000000000000000)
  directionLo := (141363846241609644763/25000000000000000000)
  directionHi := (565455384966438579053/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree139.table
  base := (-1619246779502660539047345801224086434873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-26985148509139367441478362593310000000000000)
      constant := (663431178959614159449983745021343195101608515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree139.table
  base := (-1619247448936440540763403620535886266939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-49645683862080732852983809793070000000000000)
      constant := (1247715078087347015815399964384046159819691661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141363846241609644763/25000000000000000000)
  centralHi := (565455384966438579053/100000000000000000000)
  directionLo := (567500438241984347683/100000000000000000000)
  directionHi := (141875109560496086921/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree140.table
  base := (-720403200501778758764069717858990082889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-27184458538602952664547939756850000000000000)
      constant := (673567012474074845217766147471587518660450790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree140.table
  base := (-90050437546091500282644766540965601949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-50012157142062163747014967803450000000000000)
      constant := (1266742917174276426682241236266631175509290416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567500438241984347683/100000000000000000000)
  centralHi := (141875109560496086921/25000000000000000000)
  directionLo := (569538148346662840747/100000000000000000000)
  directionHi := (142384537086665710187/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree141.table
  base := (-629920502640200846674864743120666610471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-27383768568066537887617516920390000000000000)
      constant := (683779184178581594837334121360313273495738810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree141.table
  base := (-314960385636080064792148273466916858901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5597625602449288293449569534870000000000000)
      constant := (142879317008152246571777342421112244111110444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569538148346662840747/100000000000000000000)
  centralHi := (142384537086665710187/25000000000000000000)
  directionLo := (285784296909157679659/50000000000000000000)
  directionHi := (571568593818315359319/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree142.table
  base := (-269087652087533393868527113777105725817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-27583078597530123110687094083930000000000000)
      constant := (694067694049989929273237587521676328904777740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree142.table
  base := (-6727194310169908347977768291582034401/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-50745103702025025535077283824210000000000000)
      constant := (1305227885744910665350100583817315220563679840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285784296909157679659/50000000000000000000)
  centralHi := (571568593818315359319/100000000000000000000)
  directionLo := (143397962951175540061/25000000000000000000)
  directionHi := (114718370360940432049/20000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree143.table
  base := (-890335225699177601815098109082622055413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-27782388626993708333756671247470000000000000)
      constant := (704432542065921965212691073502703611129928215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree143.table
  base := (-1424537050883961892336419510822271797/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-51111576982006456429108441834590000000000000)
      constant := (1324685015150360264811078647230859544410001875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143397962951175540061/25000000000000000000)
  centralHi := (114718370360940432049/20000000000000000000)
  directionLo := (115121599619541152883/20000000000000000000)
  directionHi := (8993874970276652569/1562500000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree144.table
  base := (-701794872322439938984292617126812471881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-27981698656457293556826248411010000000000000)
      constant := (714873728204710063244940825729243755978131955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree144.table
  base := (-701795258464003341612975870450328216559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5719783362443098591459955538330000000000000)
      constant := (149365026805808968478988591574879855145414449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115121599619541152883/20000000000000000000)
  centralHi := (8993874970276652569/1562500000000000000)
  directionLo := (577617107166459778987/100000000000000000000)
  directionHi := (144404276791614944747/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree145.table
  base := (-510729562758446044614609449805456328687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-28181008685920878779895825574550000000000000)
      constant := (725391252445346054083707278456331115605047285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree145.table
  base := (-255364954305529963917315875097385128959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-51844523541969318217170757855350000000000000)
      constant := (1364028564014259858456271040331743402559155282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577617107166459778987/100000000000000000000)
  centralHi := (144404276791614944747/25000000000000000000)
  directionLo := (289809626094722101723/50000000000000000000)
  directionHi := (579619252189444203447/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree146.table
  base := (-317139311121029625772005934005144437283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-28380318715384464002965402738090000000000000)
      constant := (735985114767435448022280123346614566288126065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree146.table
  base := (-317139620873778308668875383767222001953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-52210996821950749111201915865730000000000000)
      constant := (1383914983400845716959869023628081455572920247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289809626094722101723/50000000000000000000)
  centralHi := (579619252189444203447/100000000000000000000)
  directionLo := (18175453283924573623/3125000000000000000)
  directionHi := (581614505085586355937/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree147.table
  base := (-6051206556396995336198048735686184007/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-28579628744848049226034979901630000000000000)
      constant := (746655315151156097431592853382386669282197700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree147.table
  base := (-60512204268024577246341159672836779413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5841941122436908889470341541790000000000000)
      constant := (155993833264165210243115640073569100341499286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18175453283924573623/3125000000000000000)
  centralHi := (581614505085586355937/100000000000000000000)
  directionLo := (583602936544404816753/100000000000000000000)
  directionHi := (291801468272202408377/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree148.table
  base := (77615963873305716939641355677000881311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-28778938774311634449104557065170000000000000)
      constant := (757401853577220839675018086079041266273494395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree148.table
  base := (77615715443735077835283720763864795737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-52943943381913610899264231886490000000000000)
      constant := (1424117111910478605360496867092146812333711937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583602936544404816753/100000000000000000000)
  centralHi := (291801468272202408377/50000000000000000000)
  directionLo := (18299519251726004221/3125000000000000000)
  directionHi := (585584616055232135073/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree149.table
  base := (278780960882032047427059883789620150467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-28978248803775219672174134228710000000000000)
      constant := (768224730026843699091746755441048001117424815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree149.table
  base := (139390369206939576340917984294117471181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-53310416661895041793295389896870000000000000)
      constant := (1444432820966913797169355424134657999085083562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18299519251726004221/3125000000000000000)
  centralHi := (585584616055232135073/100000000000000000000)
  directionLo := (293779805967775238811/50000000000000000000)
  directionHi := (587559611935550477623/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree150.table
  base := (96494169444643899872395907427807150343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-29177558833238804895243711392250000000000000)
      constant := (779123944481709272380910086188665906661228175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree150.table
  base := (241235324006159614659499986578788499391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-5964098882430719187480727545250000000000000)
      constant := (162765736279404304396098107804742539752647998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293779805967775238811/50000000000000000000)
  centralHi := (587559611935550477623/100000000000000000000)
  directionLo := (2947639956792364547/500000000000000000)
  directionHi := (589527991358472909401/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree151.table
  base := (688685610528288744594604713123445090337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-29376868862702390118313288555790000000000000)
      constant := (790099496923944962413331623676135378155536965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree151.table
  base := (688685432151107758627787017243337853357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-54043363221857903581357705917630000000000000)
      constant := (1485493528522212680971821015762709921756581557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2947639956792364547/500000000000000000)
  centralHi := (589527991358472909401/100000000000000000000)
  directionLo := (591489820379401582313/100000000000000000000)
  directionHi := (295744910189700791157/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree152.table
  base := (897425238717649861490999353412609028993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-29576178892165975341382865719330000000000000)
      constant := (801151387336095761752250330299169220046894885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree152.table
  base := (448712539501142496610178031268866722351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-54409836501839334475388863928010000000000000)
      constant := (1506238526958871098087213786154100644689669902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591489820379401582313/100000000000000000000)
  centralHi := (295744910189700791157/50000000000000000000)
  directionLo := (59344516396189276341/10000000000000000000)
  directionHi := (593445163961892763411/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree153.table
  base := (1108689719984831615706490240603607309297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1782)
      previous := (1023)
      next := (0)
      square := (16073389472869776053998158350000000000000)
      linear := (-1751499348331150621438378993110000000000000)
      constant := (47781153864770665850825773721095306621290245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree153.table
  base := (554344788492495535267165116408876073349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (352)
      previous := (209)
      next := (0)
      square := (3214677894573955210799631670000000000000)
      linear := (-358015096613207616793594914630000000000000)
      constant := (9981219750290798525545990452037901786493866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59344516396189276341/10000000000000000000)
  centralHi := (593445163961892763411/100000000000000000000)
  directionLo := (595394086002757356519/100000000000000000000)
  directionHi := (14884852150068933913/2500000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree154.table
  base := (1322479042782026414631517245205544806903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-29974798951093145787522020046410000000000000)
      constant := (823484182002275053577374278167374012245974835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree154.table
  base := (661239457376844343185517841453199523721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-55142783061802196263451179948770000000000000)
      constant := (1548157812999566167407568524114499543922396642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595394086002757356519/100000000000000000000)
  centralHi := (14884852150068933913/2500000000000000000)
  directionLo := (29866832467821217783/5000000000000000000)
  directionHi := (597336649356424355661/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree155.table
  base := (192349149475863027724856576553793047171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-30174108980556731010591597209950000000000000)
      constant := (834765086223285097189563560919761847625296760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree155.table
  base := (1538793081187380647576845091572059726923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-55509256341783627157482337959150000000000000)
      constant := (1569332100545167363384917156349678927349726723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29866832467821217783/5000000000000000000)
  centralHi := (597336649356424355661/100000000000000000000)
  directionLo := (59927291585859351237/10000000000000000000)
  directionHi := (599272915858593512371/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree156.table
  base := (1757632167990564527958782742245921560629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-30373419010020316233661174373490000000000000)
      constant := (846122328348136889064740165363737356655108905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree156.table
  base := (439408016344929819163131763035382104029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-6208414402418339783501499552170000000000000)
      constant := (176738831600325372447934103886508901712257524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59927291585859351237/10000000000000000000)
  centralHi := (599272915858593512371/100000000000000000000)
  directionLo := (300601473174601199307/50000000000000000000)
  directionHi := (120240589269840479723/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree157.table
  base := (49474898712162739090071369851232302233/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-30572729039483901456730751537030000000000000)
      constant := (857555908361157239925964377144629227069067400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree157.table
  base := (1978995856629915915179567950464932385751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-56242202901746488945544653979910000000000000)
      constant := (1612109964545016382046491306090799289135338351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300601473174601199307/50000000000000000000)
  centralHi := (120240589269840479723/20000000000000000000)
  directionLo := (603126800694731999387/100000000000000000000)
  directionHi := (150781700173682999847/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree158.table
  base := (550721131665133622931495600821917527191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-30772039068947486679800328700570000000000000)
      constant := (869065826246979723783763846465658683307163980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree158.table
  base := (1101442222217184397248259433109844656677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-56608676181727919839575811990290000000000000)
      constant := (1633713540944111585229881841044577411904033754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603126800694731999387/100000000000000000000)
  centralHi := (150781700173682999847/25000000000000000000)
  directionLo := (605044537809873971463/100000000000000000000)
  directionHi := (75630567226234246433/12500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree159.table
  base := (607324473020360376797174066340235150711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-30971349098411071902869905864110000000000000)
      constant := (880652081990531259809712040181678559171109580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree159.table
  base := (2429297818478936450818172678243572018603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-6330572162412150081511885555630000000000000)
      constant := (183940023730376319959363690679752392313376267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605044537809873971463/100000000000000000000)
  centralHi := (75630567226234246433/12500000000000000000)
  directionLo := (151739053919645438601/25000000000000000000)
  directionHi := (121391243135716350881/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree160.table
  base := (2658236034512494739496615385607676711839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-31170659127874657125939483027650000000000000)
      constant := (892314675577019764670944577755403092848607355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree160.table
  base := (2658235968631791782152178746845845568777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-57341622741690781627638128011050000000000000)
      constant := (1677349982406489382967383327296546044324388977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151739053919645438601/25000000000000000000)
  centralHi := (121391243135716350881/20000000000000000000)
  directionLo := (121772378274905362869/20000000000000000000)
  directionHi := (304430945687263407173/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree161.table
  base := (72242473597588543552933902953848834267/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-31369969157338242349009060191190000000000000)
      constant := (904053606991922768082222164818544462620632600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree161.table
  base := (2889698884936798886219303841650437926639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-57708096021672212521669286021430000000000000)
      constant := (1699382847417523185747383888948692789047188039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121772378274905362869/20000000000000000000)
  centralHi := (304430945687263407173/50000000000000000000)
  directionLo := (305380810540490218941/50000000000000000000)
  directionHi := (610761621080980437883/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree162.table
  base := (3123686610383735272037113798518704032161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-31569279186801827572078637354730000000000000)
      constant := (915868876220976895777389853630927527326472645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree162.table
  base := (1561843278803680540050166455364744044971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-6452729922405960379522271559090000000000000)
      constant := (191284312064559261111333558080460822057993238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305380810540490218941/50000000000000000000)
  centralHi := (610761621080980437883/100000000000000000000)
  directionLo := (306327730055070335159/50000000000000000000)
  directionHi := (612655460110140670319/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree163.table
  base := (3360199024254796123577976685686606253737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-31768589216265412795148214518270000000000000)
      constant := (927760483250168134304243061726785146036649965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree163.table
  base := (84004974425517351763101407137481808487/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-58441042581635074309731602042190000000000000)
      constant := (1743877865871991013784439312274923607354987480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306327730055070335159/50000000000000000000)
  centralHi := (612655460110140670319/100000000000000000000)
  directionLo := (24581738516876928301/4000000000000000000)
  directionHi := (307271731460961603763/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree164.table
  base := (71984723519695281489922854585509999359/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-31967899245728998018217791681810000000000000)
      constant := (939728428065722801141639495143315097453687750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree164.table
  base := (112476129178515099871416638766580557607/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-58807515861616505203762760052570000000000000)
      constant := (1766340019265779494659860784493380032970745824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24581738516876928301/4000000000000000000)
  centralHi := (307271731460961603763/50000000000000000000)
  directionLo := (616425683142234301741/100000000000000000000)
  directionHi := (308212841571117150871/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree165.table
  base := (3840798056202189613710843674833702376971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-32167209275192583241287368845350000000000000)
      constant := (951772710654099151746067443752834699934723095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree165.table
  base := (768159603674377613178586454780182534083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-6574887682399770677532657562550000000000000)
      constant := (198771696526464588530346550276157363761749935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616425683142234301741/100000000000000000000)
  centralHi := (308212841571117150871/50000000000000000000)
  directionLo := (77287771697592878359/12500000000000000000)
  directionHi := (618302173580743026873/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree166.table
  base := (2042442327845362061590430186532342256317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-32366519304656168464356946008890000000000000)
      constant := (963893331001979562364457345884610469120756130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree166.table
  base := (81697692436737236863651801949846928657/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-59540462421579366991825076073330000000000000)
      constant := (1811693614265365936300229361196237593071842850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77287771697592878359/12500000000000000000)
  centralHi := (618302173580743026873/100000000000000000000)
  directionLo := (620172986248169566577/100000000000000000000)
  directionHi := (310086493124084783289/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree167.table
  base := (4331495965384070647813763806045988943783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-32565829334119753687426523172430000000000000)
      constant := (976090289096263233896700641607744454023766435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree167.table
  base := (270718495943109743592022265072211597361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-59906935701560797885856234083710000000000000)
      constant := (1834585055823878509153828659533785157835775376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620172986248169566577/100000000000000000000)
  centralHi := (310086493124084783289/50000000000000000000)
  directionLo := (622038172373105536891/100000000000000000000)
  directionHi := (155509543093276384223/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree168.table
  base := (4580631976361261365958740358088149998037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-32765139363583338910496100335970000000000000)
      constant := (988363584924059367840511905247565376747163465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree168.table
  base := (4580631949253183665003770668886522107277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5984)
      previous := (3553)
      next := (0)
      square := (54649524207757238583593738390000000000000)
      linear := (-6697045442393580975543043566010000000000000)
      constant := (206402177043403214764620121438268204889003053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell015.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622038172373105536891/100000000000000000000)
  centralHi := (155509543093276384223/25000000000000000000)
  directionLo := (623897782418381732833/100000000000000000000)
  directionHi := (311948891209190866417/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree169.table
  base := (4832292679842231421638468526870197295517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30294)
      previous := (17391)
      next := (0)
      square := (273247621038786192917968691950000000000000)
      linear := (-32964449393046924133565677499510000000000000)
      constant := (1000713218472680770479003907233219435092022065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree169.table
  base := (4832292655586120306855145797510769139879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (53856)
      previous := (31977)
      next := (0)
      square := (491845717869815147252343645510000000000000)
      linear := (-60639882261523659673918550104470000000000000)
      constant := (1880797226942881801877451352024285510532825279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell015.Kernel169
