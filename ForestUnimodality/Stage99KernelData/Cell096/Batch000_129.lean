import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell096.Parameters
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch000_049
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch050_099
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch100_149
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch000_049
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch050_099
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree000.table
  base := (254564412410561983995904711/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (102)
      previous := (51)
      next := (51)
      square := (914531962072456239276618820000000000000)
      linear := (-43256783196445767677995597000000000000)
      constant := (509128824821123967991809422000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree000.table
  base := (254564412410561983995904711/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (102)
      previous := (51)
      next := (51)
      square := (914531962072456239276618820000000000000)
      linear := (-43256783196445767677995597000000000000)
      constant := (509128824821123967991809422000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree001.table
  base := (28556543121945859829071132186558450999127/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-7175141786719965053928339489070872000000000000)
      constant := (2069856396324537693216017224445169820933591870870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree001.table
  base := (71328970790588465724060465235316254773923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-7182832428938518115615506305460309500000000000)
      constant := (2068053467211525307003006084313176068199215799852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49965205158052409469/100000000000000000000)
  directionHi := (4996520515805240947/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree002.table
  base := (33553936027295126614965319375326682106463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-14037040399801748813686059744382587000000000000)
      constant := (1222335395189464902150662713497425180334958958515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree002.table
  base := (167507732743054948458543127021356628086263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-14052421684238854937060393377161462000000000000)
      constant := (1220454817958892177507993973708975202698239875503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49965205158052409469/100000000000000000000)
  centralHi := (4996520515805240947/10000000000000000000)
  directionLo := (14132294156254368327/20000000000000000000)
  directionHi := (17665367695317960409/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree003.table
  base := (104299034540297705689386145615239467392509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-2322104334764836952604864444410478000000000000)
      constant := (85751505953460321633409838320655531306719273981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree003.table
  base := (10408867596048462724904328621661154291059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-2324667882171021306500586716540290500000000000)
      constant := (85586296693843573021628454413085353507871909310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14132294156254368327/20000000000000000000)
  centralHi := (17665367695317960409/25000000000000000000)
  directionLo := (1730845478886986181/2000000000000000000)
  directionHi := (86542273944349309051/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree004.table
  base := (68936286210826585700410168891964255324073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-27760837625965316333201500255006017000000000000)
      constant := (528289456300686517044808248396459868108423472113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree004.table
  base := (68781622137108710424622954765046918429569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-27791600194839528579950167520563767000000000000)
      constant := (527233971191984290705131434095447709416273751689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1730845478886986181/2000000000000000000)
  centralHi := (86542273944349309051/100000000000000000000)
  directionLo := (49965205158052409469/50000000000000000000)
  directionHi := (99930410316104818939/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree005.table
  base := (24145239669165491676435865664081734253441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-34622736239047100092959220510317732000000000000)
      constant := (394942751280087019316499616996424893024184372242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree005.table
  base := (48179363604528880705193142781717396383221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-34661189450139865401395054592264919500000000000)
      constant := (394238681207307863023683908280989788356688590301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49965205158052409469/50000000000000000000)
  centralHi := (99930410316104818939/100000000000000000000)
  directionLo := (111725595243128311219/100000000000000000000)
  directionHi := (5586279762156415561/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree006.table
  base := (35492723485494461162519845946722958242653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-4609403872458764872524104529514383000000000000)
      constant := (35775833214048414276207925473308368208662787677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree006.table
  base := (17705941425634663944613171553160982256271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-4614530967271133580315549073774008000000000000)
      constant := (35726855445727056957371766466190075981971906078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111725595243128311219/100000000000000000000)
  centralHi := (5586279762156415561/5000000000000000000)
  directionLo := (24477851506141304009/20000000000000000000)
  directionHi := (61194628765353260023/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree007.table
  base := (6749898054115554068951210300287249716761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-48346533465210667612474661020941162000000000000)
      constant := (283749044029592370930197656126336199652220652164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree007.table
  base := (107755012915122115900924151309851995931/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-48400367960740539044284828735667224500000000000)
      constant := (283505092297326191108753605223064819414728452750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24477851506141304009/20000000000000000000)
  centralHi := (61194628765353260023/50000000000000000000)
  directionLo := (66097753527264203333/50000000000000000000)
  directionHi := (132195507054528406667/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree008.table
  base := (20964376509945395822270314475681793506299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-55208432078292451372232381276252877000000000000)
      constant := (266869478299365123076273096725732680721787588819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree008.table
  base := (20916568930723109251332250197989904388773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-55269957216040875865729715807368377000000000000)
      constant := (266779872942759636972983910873119354323116292813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66097753527264203333/50000000000000000000)
  centralHi := (132195507054528406667/100000000000000000000)
  directionLo := (14132294156254368327/10000000000000000000)
  directionHi := (141322941562543683271/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree009.table
  base := (16409315884492748018576246108615546805881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-766300378905854754715927179402032000000000000)
      constant := (3262510713416961638380552865902417437492567281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree009.table
  base := (3274025174501066816612809144716020467997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-767154894707916206014501270111969500000000000)
      constant := (3263013816026548285142096362444354682421998985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14132294156254368327/10000000000000000000)
  centralHi := (141322941562543683271/100000000000000000000)
  directionLo := (18736951934269653551/12500000000000000000)
  directionHi := (149895615474157228409/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree010.table
  base := (1280414569526334155559280746341418603193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-68932229304456018891747821786876307000000000000)
      constant := (272090811141231327730483931758693718280686488330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree010.table
  base := (6385443018533441040669369933841574498603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-69009135726641549508619489950770682000000000000)
      constant := (272250432755178520286359213772261099670936302086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736951934269653551/12500000000000000000)
  centralHi := (149895615474157228409/100000000000000000000)
  directionLo := (79001926028519505721/50000000000000000000)
  directionHi := (158003852057039011443/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree011.table
  base := (9851097720838671700468149419122140127937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-75794127917537802651505542042188022000000000000)
      constant := (288195525444931533069893804363259928603293354697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree011.table
  base := (2455540743024436883789391930000426270517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-75878724981941886330064377022471834500000000000)
      constant := (288470364606483652076443088994539578772523862708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79001926028519505721/50000000000000000000)
  centralHi := (158003852057039011443/100000000000000000000)
  directionLo := (165715838082390115739/100000000000000000000)
  directionHi := (8285791904119505787/5000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree012.table
  base := (460931264359223779918722343662632413227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-9184002947846620712362584699722193000000000000)
      constant := (34589809309398779578521612068575535553986611888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree012.table
  base := (7349329779371508349130897044912089769009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-9194257137471358127945473788241443000000000000)
      constant := (34633261920718915240557469065952417636952562481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165715838082390115739/100000000000000000000)
  centralHi := (8285791904119505787/5000000000000000000)
  directionLo := (173084547888698618101/100000000000000000000)
  directionHi := (86542273944349309051/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree013.table
  base := (2633114005702187469516164771044305534579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-529691864755629409295982145282908000000000000)
      constant := (2015605974703706998594918299821612333202351142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree013.table
  base := (5243431659529663021746792540247462188641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-530283452618595029425764208082095500000000000)
      constant := (2018629684530916418582316336127143210446078209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173084547888698618101/100000000000000000000)
  centralHi := (86542273944349309051/50000000000000000000)
  directionLo := (180152109186435761701/100000000000000000000)
  directionHi := (90076054593217880851/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree014.table
  base := (1726201637519593170965516757464721960889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-96379823756783153930778702808123167000000000000)
      constant := (375656608424961952887594076615552865000120873218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree014.table
  base := (107249921611264432675958552709907785639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-96487492747842896794399038237575292000000000000)
      constant := (376292744558392278519917221916871642664120523488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180152109186435761701/100000000000000000000)
  centralHi := (90076054593217880851/50000000000000000000)
  directionLo := (186952678961302235377/100000000000000000000)
  directionHi := (93476339480651117689/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree015.table
  base := (1882025824652883501599293012226892443649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-11471302485540548632281824784826098000000000000)
      constant := (46221518482441271342600136761040642389691978241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree015.table
  base := (232967490359167054747718006181039501143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-11484120222571470401760436145475160500000000000)
      constant := (46306771612794171864475756751080875798926344696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186952678961302235377/100000000000000000000)
  centralHi := (93476339480651117689/50000000000000000000)
  directionLo := (193514407466973906891/100000000000000000000)
  directionHi := (48378601866743476723/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree016.table
  base := (32297079607501300659126083667951372521/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-110103620982946721450294143318746597000000000000)
      constant := (461370927812436279966782464432044864768555897616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree016.table
  base := (100075518745842494514166929252113432309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-110226671258443570437288812380977597000000000000)
      constant := (462275802816786007830528898503805075149552048145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193514407466973906891/100000000000000000000)
  centralHi := (48378601866743476723/25000000000000000000)
  directionLo := (199860820632209637877/100000000000000000000)
  directionHi := (99930410316104818939/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree017.table
  base := (-673223290917335056341519470812168061071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-116965519596028505210051863574058312000000000000)
      constant := (511572532158092642364667149428948140354447513849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree017.table
  base := (-687864915826042248012653212517913078801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-117096260513743907258733699452678749500000000000)
      constant := (512621701325442792491621385539220596233336055719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199860820632209637877/100000000000000000000)
  centralHi := (99930410316104818939/50000000000000000000)
  directionLo := (103005909236153219809/50000000000000000000)
  directionHi := (206011818472306439619/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree018.table
  base := (-427943141887630537726967684996343118619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-1528733558137164061355673874436667000000000000)
      constant := (6992909069799618176667233802381643715409371124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree018.table
  base := (-13475287408805435344494284857362693409/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-1530442589741286963952822055856542000000000000)
      constant := (7007727612826266303677612024180858671857374848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103005909236153219809/50000000000000000000)
  centralHi := (206011818472306439619/100000000000000000000)
  directionLo := (105992206171907762453/50000000000000000000)
  directionHi := (211984412343815524907/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree019.table
  base := (-2618389683490893585878966050321516275729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-130689316822192072729567304084681742000000000000)
      constant := (625789061705447825152823152852248416185617685351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree019.table
  base := (-657505079049806305992511530082356638673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-130835439024344580901623473596081054500000000000)
      constant := (627147428106806252891248548240273767566427421148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105992206171907762453/50000000000000000000)
  centralHi := (211984412343815524907/100000000000000000000)
  directionLo := (27224159997153457567/12500000000000000000)
  directionHi := (217793279977227660537/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree020.table
  base := (-3409202682126920853065608059907260254987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-137551215435273856489325024339993457000000000000)
      constant := (689546022393364108966009210963669915601456484253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree020.table
  base := (-136781345325858098855307124030380079841/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-137705028279644917723068360667782207000000000000)
      constant := (691069456570105706435615631568011433226322886975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27224159997153457567/12500000000000000000)
  centralHi := (217793279977227660537/100000000000000000000)
  directionLo := (111725595243128311219/50000000000000000000)
  directionHi := (223451190486256622439/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree021.table
  base := (-4097661767249596227192498098739906320277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-16045901560928404472120304955033908000000000000)
      constant := (84177679702479925024559823046147494153048243307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree021.table
  base := (-1026704536320498393956332258782632533267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-16063846392771694949390360859942595500000000000)
      constant := (84366076260204865880578488234405974233287289588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111725595243128311219/50000000000000000000)
  centralHi := (223451190486256622439/100000000000000000000)
  directionLo := (5724233368769328551/2500000000000000000)
  directionHi := (228969334750773142041/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree022.table
  base := (-293439984902629593120035373717173359721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-151275012661437424008840464850616887000000000000)
      constant := (829866714583485637887934970526543957369987411184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree022.table
  base := (-117578455049445713291923494752740027429/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-151444206790245591365958134811184512000000000000)
      constant := (831741546850065957298345628779107505674836706040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5724233368769328551/2500000000000000000)
  centralHi := (228969334750773142041/100000000000000000000)
  directionLo := (187486068572911947/80000000000000000)
  directionHi := (234357585716139933751/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree023.table
  base := (-521081329292410750883214658576294063821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-298935560065253700885818875436538000000000000)
      constant := (1713195064817565783116151051610062293103543310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree023.table
  base := (-5217962032719854676620454799529238768419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-299269935813886442698304389192600500000000000)
      constant := (1717091633442053750881383193638409578624112309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187486068572911947/80000000000000000)
  centralHi := (234357585716139933751/100000000000000000000)
  directionLo := (14976544122860939917/6250000000000000000)
  directionHi := (239624705965775038673/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree024.table
  base := (-1413240929974375985387757362618617354983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-18333201098622332392039545040137813000000000000)
      constant := (109642416072082229836354448632287444634497933412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree024.table
  base := (-5659262620027248148697061665177334477769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-18353709477871807223205323217176313000000000000)
      constant := (109892970206973253059960666537856074583176762679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14976544122860939917/6250000000000000000)
  centralHi := (239624705965775038673/100000000000000000000)
  directionLo := (244778515061413040091/100000000000000000000)
  directionHi := (61194628765353260023/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree025.table
  base := (-6028220534440925697462767159538776255683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-171860708500682775288113625616552032000000000000)
      constant := (1071322649153477214700453163967627368918720413477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree025.table
  base := (-1206752242156725346093221933096792229749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-172052974556146601830292796026287969500000000000)
      constant := (1073778648384200459884862837824950435239749908655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244778515061413040091/100000000000000000000)
  centralHi := (61194628765353260023/25000000000000000000)
  directionLo := (249826025790262047347/100000000000000000000)
  directionHi := (62456506447565511837/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree026.table
  base := (-6342261545442253986928305947783436306803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-1057530219608074313892729857229963000000000000)
      constant := (6863087497381778194515665620303660537689798253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree026.table
  base := (-6347127588101041073932966815866099800687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-1058713395334005554152293982828338000000000000)
      constant := (6878853053423017429493300248555066177140362737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249826025790262047347/100000000000000000000)
  centralHi := (62456506447565511837/25000000000000000000)
  directionLo := (995209203521781643/390625000000000000)
  directionHi := (254773556101576100609/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree027.table
  base := (-824984896895742725721465937667311728189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-2291166737368473367995420569471302000000000000)
      constant := (15461289557112320440748393190235828501005401688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree027.table
  base := (-412759154239984712166736070870180491737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-2293730284774657721891142841601114500000000000)
      constant := (15496847362551052255137402584105729604856527408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (995209203521781643/390625000000000000)
  centralHi := (254773556101576100609/100000000000000000000)
  directionLo := (16226676364565495447/6250000000000000000)
  directionHi := (259626821833047927153/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree028.table
  base := (-680511951180220459037291934747342947707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-192446404339928126567386786382487177000000000000)
      constant := (1348801350688455767714418575390118875936957659330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree028.table
  base := (-6808856627928679819363281359337032630207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-192661742322047612294627457241391427000000000000)
      constant := (1351904812665000899096995364840885906611975983433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16226676364565495447/6250000000000000000)
  centralHi := (259626821833047927153/100000000000000000000)
  directionLo := (66097753527264203333/25000000000000000000)
  directionHi := (264391014109056813333/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree029.table
  base := (-3480699519558775574635504901677824258691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-199308302953009910327144506637798892000000000000)
      constant := (1449147736342311968941174935309039193956200077258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree029.table
  base := (-3482333845751322725545203393050118532233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-199531331577347949116072344313092579500000000000)
      constant := (1452482004202438905005867846938949278530298685854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66097753527264203333/25000000000000000000)
  centralHi := (264391014109056813333/100000000000000000000)
  directionLo := (67267716099599807413/25000000000000000000)
  directionHi := (269070864398399229653/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree030.table
  base := (-7071602862721068668131872055500598234277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-22907800174010188231878025210345623000000000000)
      constant := (172598079850023929010949559459700221655316617307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree030.table
  base := (-7074458384927234842597038572499560292317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-22933435648072031770835247931643748000000000000)
      constant := (172995040526296520587010194160315164730259110947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67267716099599807413/25000000000000000000)
  centralHi := (269070864398399229653/100000000000000000000)
  directionLo := (68417674888596958381/25000000000000000000)
  directionHi := (10946827982175513341/4000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree031.table
  base := (-7138167486527453819308762950751899273911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-213032100179173477846659947148422322000000000000)
      constant := (1661488653715361242612922540130369289881559697809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree031.table
  base := (-892582415960256889722832640842925005913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-213270510087948622758962118456494884500000000000)
      constant := (1665307292982910435053484304100710162510173982776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68417674888596958381/25000000000000000000)
  centralHi := (10946827982175513341/4000000000000000000)
  directionLo := (69548622165123749599/25000000000000000000)
  directionHi := (278194488660494998397/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree032.table
  base := (-223848457215932084395156019660282776787/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-219893998792255261606417667403734037000000000000)
      constant := (1773450640594764351385053978932182550152630350496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree032.table
  base := (-7165322849411574866786464553290468568703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-220140099343248959580407005528196037000000000000)
      constant := (1777522927035037998266455784415744538378640030857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69548622165123749599/25000000000000000000)
  centralHi := (278194488660494998397/100000000000000000000)
  directionLo := (282645883125087366541/100000000000000000000)
  directionHi := (141322941562543683271/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree033.table
  base := (-3574145076186413425075213899886902767621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-25195099711704116151797265295449528000000000000)
      constant := (209917343848173957087621458217328800539594469622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree033.table
  base := (-71501818975642079139058293362043229031/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-25223298733172144044650210288877465500000000000)
      constant := (210398857531892187525913263251424728781384612100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282645883125087366541/100000000000000000000)
  centralHi := (141322941562543683271/50000000000000000000)
  directionLo := (287028251177557109919/100000000000000000000)
  directionHi := (1793926569859731937/625000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree034.table
  base := (-3547526890936370379942958650737653290879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-233617796018418829125933107914357467000000000000)
      constant := (2008894387285931969360724687491735653419024496402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree034.table
  base := (-7096699755850438303540535219895077864969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-233879277853849633223296779671598342000000000000)
      constant := (2013497068897698423745450897218613521834806420911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287028251177557109919/100000000000000000000)
  centralHi := (1793926569859731937/625000000000000000)
  directionLo := (145672353846339938897/50000000000000000000)
  directionHi := (58268941538535975559/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree035.table
  base := (-7004681120576632448598792320635809366451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-240479694631500612885690828169669182000000000000)
      constant := (2132356542003564546183906226952472490740723046069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree035.table
  base := (-7006112014865148353359041330937665042087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-240748867109149970044741666743299494500000000000)
      constant := (2137236032861227587302518257218748464616487789153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145672353846339938897/50000000000000000000)
  centralHi := (58268941538535975559/20000000000000000000)
  directionLo := (7389953502349462883/2500000000000000000)
  directionHi := (295598140093978515321/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree036.table
  base := (-1375643820483255268603299886389158182161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-3053599916599782674635167264505937000000000000)
      constant := (27896728116472693141366728960358438846783122195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree036.table
  base := (-687946200625886883987918521913497304171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-3057017979808028479829463627345687000000000000)
      constant := (27960482153225841495633978796114113775098084290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7389953502349462883/2500000000000000000)
  centralHi := (295598140093978515321/100000000000000000000)
  directionLo := (18736951934269653551/6250000000000000000)
  directionHi := (299791230948314456817/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree037.table
  base := (-6716551941879477360034359677150319777357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-254203491857664180405206268680292612000000000000)
      constant := (2390723290555689400123717097688721700125845054283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree037.table
  base := (-1343526144093805130082396272418665562993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-254488045619750643687631440886701799500000000000)
      constant := (2396179753872381344025082120587786640479284436835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736951934269653551/6250000000000000000)
  centralHi := (299791230948314456817/100000000000000000000)
  directionLo := (7598161943851613301/2500000000000000000)
  directionHi := (303926477754064532041/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree038.table
  base := (-6520426425694251451086788418619043985601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-261065390470745964164963988935604327000000000000)
      constant := (2525616073525866333522933141058829030240106084919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree038.table
  base := (-6521362067848761508014890008181046182581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-261357634875050980509076327958402952000000000000)
      constant := (2531372744231804149619398911229564291446217157539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7598161943851613301/2500000000000000000)
  centralHi := (303926477754064532041/100000000000000000000)
  directionLo := (308006210337516003113/100000000000000000000)
  directionHi := (154003105168758001557/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree039.table
  base := (-3145236636423443610382811059361196535941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (485622)
      previous := (242811)
      next := (242811)
      square := (4354086671426964155195982202020000000000000)
      linear := (-176152063828946579832164174353002000000000000)
      constant := (1751682287314440102865013069955287874084769798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree039.table
  base := (-15728210521253939481625042740160143737/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (485622)
      previous := (242811)
      next := (242811)
      square := (4354086671426964155195982202020000000000000)
      linear := (-176349259783268453208758195286064500000000000)
      constant := (1755669609914600347886781908964983350392257200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308006210337516003113/100000000000000000000)
  centralHi := (154003105168758001557/50000000000000000000)
  directionLo := (62406521240320523761/20000000000000000000)
  directionHi := (156016303100801309403/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree040.table
  base := (-6027225174395109542552801518414275711631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-274789187696909531684479429446227757000000000000)
      constant := (2806797489521707204353425434999469527305462634489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree040.table
  base := (-6027927562898963002847034078052500833781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-275096813385651654151966102101805257000000000000)
      constant := (2813178110187523944121564093748166515709690730339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62406521240320523761/20000000000000000000)
  centralHi := (156016303100801309403/50000000000000000000)
  directionLo := (79001926028519505721/25000000000000000000)
  directionHi := (63201540822815604577/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree041.table
  base := (-2865566014653770377107843204218553731621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-281651086309991315444237149701539472000000000000)
      constant := (2953079007140364558955036889506433864547474858598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree041.table
  base := (-5731740019931070507597854384750126048977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-281966402640951990973410989173506409500000000000)
      constant := (2959783401375166481316950411605482937671852985063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79001926028519505721/25000000000000000000)
  centralHi := (63201540822815604577/20000000000000000000)
  directionLo := (319933416175830172213/100000000000000000000)
  directionHi := (159966708087915086107/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree042.table
  base := (-1350643453057000006754080244259286139507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-32056998324785899911554985550761243000000000000)
      constant := (344794506698007973551821044879171131154309648948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree042.table
  base := (-5403099778555405696858173597388585361921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-32092887988472480866095097360578618000000000000)
      constant := (345576290169163303461136719634935108408030106111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319933416175830172213/100000000000000000000)
  centralHi := (159966708087915086107/50000000000000000000)
  directionLo := (323811538572088592581/100000000000000000000)
  directionHi := (161905769286044296291/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree043.table
  base := (-1008374288252989998516313673487297534659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-295374883536154882963752590212162902000000000000)
      constant := (3257009825024443825301347049676545353994600050105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree043.table
  base := (-630290773911806131205255718903304892697/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-295705581151552664616300763316908714500000000000)
      constant := (3264385428044209849159753118045667434711746085944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323811538572088592581/100000000000000000000)
  centralHi := (161905769286044296291/50000000000000000000)
  directionLo := (163821880589032951609/50000000000000000000)
  directionHi := (327643761178065903219/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree044.table
  base := (-929859191334064394960093711862514652811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-302236782149236666723510310467474617000000000000)
      constant := (3414654838634646153064662497677374843147237734545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree044.table
  base := (-4649688920510171948463052420570898940283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-302575170406853001437745650388609867000000000000)
      constant := (3422377898185516204456502502386941554171020520877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163821880589032951609/50000000000000000000)
  centralHi := (327643761178065903219/100000000000000000000)
  directionLo := (331431676164780231479/100000000000000000000)
  directionHi := (8285791904119505787/2500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree045.table
  base := (-528134534118023010534353770334491856893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-3816033095831091981274913959540572000000000000)
      constant := (44149184486823158981909961139506184685515271256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree045.table
  base := (-845083133998404195788940157004722287241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-3820305674841399237767784413090259500000000000)
      constant := (44248918185601529525804581843750486692116836795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331431676164780231479/100000000000000000000)
  centralHi := (8285791904119505787/2500000000000000000)
  directionLo := (167588392864692466829/50000000000000000000)
  directionHi := (335176785729384933659/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree046.table
  base := (-1884702863045748937330599212137036164893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-597278978025331255657893669145743000000000000)
      constant := (7072392702040692729139784046530172723877559446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree046.table
  base := (-3769698713539176010405170850041941855587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-597947729522596739282864696657868000000000000)
      constant := (7088350586468373065636122713520059795438869557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167588392864692466829/50000000000000000000)
  centralHi := (335176785729384933659/100000000000000000000)
  directionLo := (169440254528232079449/50000000000000000000)
  directionHi := (338880509056464158899/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree047.table
  base := (-3282447603292996620468268331938565952133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-322822477988482018002783471233409762000000000000)
      constant := (3910289044034181058031956723531578457677881971027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree047.table
  base := (-1641350203861117205310477156940000124143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-323183938172754011902080311603713324500000000000)
      constant := (3919101984107631378853112383832343312250166648434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169440254528232079449/50000000000000000000)
  centralHi := (338880509056464158899/100000000000000000000)
  directionLo := (17127209430089199/5000000000000000)
  directionHi := (342544188601783980001/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree048.table
  base := (-1382169906573053750069937491975364603133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-36631597400173755751393465720969053000000000000)
      constant := (453673650970461298324906122180001661724075520006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree048.table
  base := (-2764557846882763610247010719844157062289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-36672614158672705413725022075046053000000000000)
      constant := (454694994651693367213963869710651411630268709999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17127209430089199/5000000000000000)
  centralHi := (342544188601783980001/100000000000000000000)
  directionLo := (346169095777397236203/100000000000000000000)
  directionHi := (86542273944349309051/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree049.table
  base := (-1107599415025128909658139599891838695941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-336546275214645585522298911744033192000000000000)
      constant := (4259616340032287895146865747320511869994056942758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree049.table
  base := (-138461674614701892780926753959078428619/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-336923116683354685544970085747115629500000000000)
      constant := (4269195525220374662985519084842174105459455484176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346169095777397236203/100000000000000000000)
  centralHi := (86542273944349309051/25000000000000000000)
  directionLo := (174878218053183433143/50000000000000000000)
  directionHi := (349756436106366866287/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree050.table
  base := (-817561512775117060822234618170325767581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-343408173827727369282056631999344907000000000000)
      constant := (4439948775572917176295213330463481262380503545078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree050.table
  base := (-204410624871122580618278616702614106599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-343792705938655022366414972818816782000000000000)
      constant := (4449922996315447259839053407945942490561350935048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174878218053183433143/50000000000000000000)
  centralHi := (349756436106366866287/100000000000000000000)
  directionLo := (22081709619147450511/6250000000000000000)
  directionHi := (353307353906359208177/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree051.table
  base := (-512097740958722504346254173818575438377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-38918896937867683671312705806072958000000000000)
      constant := (513784395968594409570856238754241302357705840814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree051.table
  base := (-1024335002912533440506293829071213424031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-38962477243772817687539984432279770500000000000)
      constant := (514937418603784994323104209497170348116228841121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22081709619147450511/6250000000000000000)
  centralHi := (353307353906359208177/100000000000000000000)
  directionLo := (356822936553691321619/100000000000000000000)
  directionHi := (17841146827684566081/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree052.table
  base := (-38248636844034811913638406193746277851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-2113206929312964123086225281124073000000000000)
      constant := (28473066250508972042393888600310180157403625010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree052.table
  base := (-95651625778890118350158152720388663707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-2115573280764826603605353532320823000000000000)
      constant := (28536901383807515877988875774584374764595275028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356822936553691321619/100000000000000000000)
  centralHi := (17841146827684566081/5000000000000000000)
  directionLo := (180152109186435761701/50000000000000000000)
  directionHi := (360304218372871523403/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree053.table
  base := (289945051611671329648107566401437944483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-363993869666972720561329792765280052000000000000)
      constant := (5003614244275077692442488707468726438185152699323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree053.table
  base := (14492082389951381378409630251600603813/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-364401473704556032830749634033920239500000000000)
      constant := (5014821269423512355772427962922895213420132341060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180152109186435761701/50000000000000000000)
  centralHi := (360304218372871523403/100000000000000000000)
  directionLo := (2910017473528538457/800000000000000000)
  directionHi := (181876092095533653563/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree054.table
  base := (248262181487446200436845799590194897857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-4578466275062401287914660654575207000000000000)
      constant := (64185893149158461476745613820316897556253254628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree054.table
  base := (992959754618005745522381389138042581873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-4583593369874769995706105198834832000000000000)
      constant := (64329521163546285252497140560453049082362028073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2910017473528538457/800000000000000000)
  centralHi := (181876092095533653563/50000000000000000000)
  directionLo := (45895971574014945017/12500000000000000000)
  directionHi := (367167772592119560137/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree055.table
  base := (863391190836371935011957083696070688349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-377717666893136288080845233275903482000000000000)
      constant := (5398277192637878131324888911157481513516172409738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree055.table
  base := (1726705854675704445539570649546982610953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-378140652215156706473639408177322544500000000000)
      constant := (5410345864462834277854370244521145160762671541393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45895971574014945017/12500000000000000000)
  centralHi := (367167772592119560137/100000000000000000000)
  directionLo := (46318984862571586729/12500000000000000000)
  directionHi := (370551878900572693833/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree056.table
  base := (311388789521801083781974743786950881/1250000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-384579565506218071840602953531215197000000000000)
      constant := (5601273528403461935257865795698560619821558088000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree056.table
  base := (1245522257347236823501294304909207201589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-385010241470457043295084295249023697000000000000)
      constant := (5613784963480861002195295822603410235850739826618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46318984862571586729/12500000000000000000)
  centralHi := (370551878900572693833/100000000000000000000)
  directionLo := (74781071584520894151/20000000000000000000)
  directionHi := (93476339480651117689/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree057.table
  base := (1643001187985234902352550279983865960527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-43493496013255539511151185976280768000000000000)
      constant := (645338459335855897901498297902449131250767337886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree057.table
  base := (821486453707955341960857834109239505567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-43542203413973042235169909146747205500000000000)
      constant := (646778699404150927754916369827890590435464033212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74781071584520894151/20000000000000000000)
  centralHi := (93476339480651117689/25000000000000000000)
  directionLo := (94307256616907940679/25000000000000000000)
  directionHi := (377229026467631762717/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree058.table
  base := (513929136779714697859540825356994823947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-398303362732381639360118394041838627000000000000)
      constant := (6018594825078085165559006556949927830877684364056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree058.table
  base := (82227689816114231148251988413471194401/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-398749419981057716937974069392426002000000000000)
      constant := (6032015674981507977949131374436137718102607394050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94307256616907940679/25000000000000000000)
  centralHi := (377229026467631762717/100000000000000000000)
  directionLo := (95130916417917042237/25000000000000000000)
  directionHi := (380523665671668168949/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree059.table
  base := (2483690481199270866264885422493787651127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-405165261345463423119876114297150342000000000000)
      constant := (6232919445815652086782602770284803621974841598174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree059.table
  base := (1241834802375441291463450525232658503779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-405619009236358053759418956464127154500000000000)
      constant := (6246806950029967439943615578278193003491541226796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95130916417917042237/25000000000000000000)
  centralHi := (380523665671668168949/100000000000000000000)
  directionLo := (383790023141156913503/100000000000000000000)
  directionHi := (11993438223161153547/3125000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree060.table
  base := (5853827814917166780794502100174603243559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-45780795550949467431070426061384673000000000000)
      constant := (716779984965557963541912495276620204841196763431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree060.table
  base := (2926895978646585386648276015020103452841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-45832066499073154508984871503980923000000000000)
      constant := (718375776593044493310013864821324875838173888338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383790023141156913503/100000000000000000000)
  centralHi := (11993438223161153547/3125000000000000000)
  directionLo := (387028814933947813783/100000000000000000000)
  directionHi := (48378601866743476723/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree061.table
  base := (1692689577428023474861491840741246559447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-418889058571626990639391554807773772000000000000)
      constant := (6672895970601802246626725254241788534443703284028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree061.table
  base := (6770727523535700798064210447348290995919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-419358187746958727402308730607529459500000000000)
      constant := (6687740682756215805696271662048190957957543516039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387028814933947813783/100000000000000000000)
  centralHi := (48378601866743476723/12500000000000000000)
  directionLo := (195120363696144163751/50000000000000000000)
  directionHi := (390240727392288327503/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree062.table
  base := (7718159489323937738890923985858242568503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-425750957184708774399149275063085487000000000000)
      constant := (6898547669719797863750383336181159258753205672943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree062.table
  base := (964766633053624896152400155388266734261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-426227777002259064223753617679230612000000000000)
      constant := (6913882937278277291381127104662194724370164644328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195120363696144163751/50000000000000000000)
  centralHi := (390240727392288327503/100000000000000000000)
  directionLo := (393426418841120226689/100000000000000000000)
  directionHi := (39342641884112022669/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree063.table
  base := (2174005102571882975372126117087565456949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-5340899454293710594554407349609842000000000000)
      constant := (87999689911075474649602863166410814945166790196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree063.table
  base := (1086999716842436587968966241362896246499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-5346881064908140753644425984579404500000000000)
      constant := (88195168819358420198491557551193682876791056792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393426418841120226689/100000000000000000000)
  centralHi := (39342641884112022669/10000000000000000000)
  directionLo := (198293260581792609999/50000000000000000000)
  directionHi := (396586521163585219999/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree064.table
  base := (9704331830107888186830564432322011594423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-439474754410872341918664715573708917000000000000)
      constant := (7361177542904397145580591225376733000842793860463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree064.table
  base := (9704312376825944392245986575892169423123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-439966955512859737866643391822632917000000000000)
      constant := (7377517827710595017166157424258864270926326165163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198293260581792609999/50000000000000000000)
  centralHi := (396586521163585219999/100000000000000000000)
  directionLo := (79944328252883855151/20000000000000000000)
  directionHi := (99930410316104818939/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree065.table
  base := (2148617188577424918768054546086836123279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-2641045284165409027682972993071128000000000000)
      constant := (44959500553345489705252197695738842642731909355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree065.table
  base := (5371534629025798194593309097924992445687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-2644003223480237128331883307067065500000000000)
      constant := (45059232788817893921930476501003907330735484526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79944328252883855151/20000000000000000000)
  centralHi := (99930410316104818939/25000000000000000000)
  directionLo := (80566472486166939493/20000000000000000000)
  directionHi := (201416181215417348733/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree066.table
  base := (11812276156040946057344441994374347215373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-50355394626337323270908906231592483000000000000)
      constant := (870989887432223486314008563783510647138614054157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree066.table
  base := (2362452369810829605418492977189463109533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-50411792669273379056614796218448358000000000000)
      constant := (872920685320518462288693704174477036302991187985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80566472486166939493/20000000000000000000)
  centralHi := (201416181215417348733/50000000000000000000)
  directionLo := (405919245599532554257/100000000000000000000)
  directionHi := (202959622799766277129/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree067.table
  base := (12911896901718467250123025793086866584143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-460060450250117693197937876339644062000000000000)
      constant := (8083437682708781598565715466742319991906106435783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree067.table
  base := (12911884636516254733458469985839476112239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-460575723278760748330978053037736374500000000000)
      constant := (8101345267509338482849887360750953742519857585959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405919245599532554257/100000000000000000000)
  centralHi := (202959622799766277129/50000000000000000000)
  directionLo := (408982830537639924553/100000000000000000000)
  directionHi := (204491415268819962277/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree068.table
  base := (14041943477531720397710767425939438064863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-466922348863199476957695596594955777000000000000)
      constant := (8331741646919445302139134147094285416397382182103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree068.table
  base := (14041932965068403623042605306694579317159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-467445312534061085152422940109437527000000000000)
      constant := (8350187606472471164023447270680751062428199872479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408982830537639924553/100000000000000000000)
  centralHi := (204491415268819962277/50000000000000000000)
  directionLo := (103005909236153219809/25000000000000000000)
  directionHi := (412023636944612879237/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree069.table
  base := (15202411912039480844292625222924688180933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (155142)
      previous := (77571)
      next := (77571)
      square := (1391003114312205939939737225220000000000000)
      linear := (-99513599553934312269996495872772000000000000)
      constant := (1802944938198463834611324711476564888223199093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree069.table
  base := (7601201451895640600512001471613269683877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (155142)
      previous := (77571)
      next := (77571)
      square := (1391003114312205939939737225220000000000000)
      linear := (-99625058136811892874158333791459500000000000)
      constant := (1806934080300018206871063674442353769503353834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103005909236153219809/25000000000000000000)
  centralHi := (412023636944612879237/100000000000000000000)
  directionLo := (83008433096295084861/20000000000000000000)
  directionHi := (207521082740737712153/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree070.table
  base := (3278659770227608982393461325884903663969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-480646146089363044477211037105579207000000000000)
      constant := (8839675269950426399688711549569531617847309490445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree070.table
  base := (3278658226698009147415595241376357144719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-481184491044661758795312714252839832000000000000)
      constant := (8859221892981198657830794668282725846500984444195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83008433096295084861/20000000000000000000)
  centralHi := (207521082740737712153/50000000000000000000)
  directionLo := (418038898733166573407/100000000000000000000)
  directionHi := (13063715585411455419/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree071.table
  base := (4403650365527389476162889494677127247959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-487508044702444828236968757360890922000000000000)
      constant := (9099304883968993028309270285937295306590209549116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree071.table
  base := (17614594851508473005665245440958503319857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-488054080299962095616757601324540984500000000000)
      constant := (9119413796195525291515446405081096995657306388217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418038898733166573407/100000000000000000000)
  centralHi := (13063715585411455419/3125000000000000000)
  directionLo := (210507151054616767167/50000000000000000000)
  directionHi := (84202860421846706867/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree072.table
  base := (9433158676291758609934607782454270818907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-6103332633525019901194154044644477000000000000)
      constant := (115589008339435563739381623061904727530962209414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree072.table
  base := (18866311691353834409215688394246209274701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-6110168759941511511582746770323977000000000000)
      constant := (115844306775487092014686773802041256855367544101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210507151054616767167/50000000000000000000)
  centralHi := (84202860421846706867/20000000000000000000)
  directionLo := (105992206171907762453/25000000000000000000)
  directionHi := (423968824687631049813/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree073.table
  base := (20148444502093610689656472283740973281797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-501231841928608395756484197871514352000000000000)
      constant := (9629889629895120892726256377967159468879140621357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree073.table
  base := (20148439654828009369975451291585664626971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-501793258810562769259647375467943289500000000000)
      constant := (9651147036368072418453827932145866374471707584051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105992206171907762453/25000000000000000000)
  centralHi := (423968824687631049813/100000000000000000000)
  directionLo := (5336286250074482667/1250000000000000000)
  directionHi := (426902900005958613361/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree074.table
  base := (670655662633509149407229823822129881997/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-508093740541690179516241918126826067000000000000)
      constant := (9900844734814885557824581179376988292440432561824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree074.table
  base := (21460977054718904227775386514675846916411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-508662848065863106081092262539644442000000000000)
      constant := (9922688346638464868097708828358548596791598844691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5336286250074482667/1250000000000000000)
  centralHi := (426902900005958613361/100000000000000000000)
  directionLo := (107454236701020706471/25000000000000000000)
  directionHi := (85963389360816565177/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree075.table
  base := (45607852036059508848794456557878673369/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-57217293239419107030666626486904198000000000000)
      constant := (1130619442201994465168197130325847505437878860500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree075.table
  base := (142524515415056426804572313354124405059/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-57281381924573715878059683290149510500000000000)
      constant := (1133112529923254590110426012809067688176943708960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107454236701020706471/25000000000000000000)
  centralHi := (85963389360816565177/20000000000000000000)
  directionLo := (432711369721746545253/100000000000000000000)
  directionHi := (216355684860873272627/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree076.table
  base := (24177277726320907936852267679406033371499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-521817537767853747035757358637449497000000000000)
      constant := (10454080356091105900194767758224632421445075950019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree076.table
  base := (24177274687013745100082755884941497817453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-522402026576463779723982036683046747000000000000)
      constant := (10477120295669885507077625830495720944556627367893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432711369721746545253/100000000000000000000)
  centralHi := (216355684860873272627/50000000000000000000)
  directionLo := (27224159997153457567/6250000000000000000)
  directionHi := (435586559954455321073/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree077.table
  base := (12790517650660518117819318712156611785671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-528679436380935530795515078892761212000000000000)
      constant := (10736360856191379538782395644489941501478125237502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree077.table
  base := (25581032700877603728549410870312540235479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-529271615831764116545426923754747899500000000000)
      constant := (10760010918365397805869307968894808392005081704399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27224159997153457567/6250000000000000000)
  centralHi := (435586559954455321073/100000000000000000000)
  directionLo := (438442895870651058569/100000000000000000000)
  directionHi := (43844289587065105857/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree078.table
  base := (168844986718837828136682053557358376033/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (485622)
      previous := (242811)
      next := (242811)
      square := (4354086671426964155195982202020000000000000)
      linear := (-352098182113094881364413411668687000000000000)
      constant := (7246822139272221631744467894157821816526898080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree078.table
  base := (27015195650439450491537455669626458164017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (485622)
      previous := (242811)
      next := (242811)
      square := (4354086671426964155195982202020000000000000)
      linear := (-352492574021738628117601453534812000000000000)
      constant := (7262777535296394087204665005669733504818884937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438442895870651058569/100000000000000000000)
  centralHi := (43844289587065105857/10000000000000000000)
  directionLo := (55160092949116193761/12500000000000000000)
  directionHi := (441280743592929550089/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree079.table
  base := (14239882357176062566298256122898685188717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-542403233607099098315030519403384642000000000000)
      constant := (11312247203707762644853645923945219727625651139754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree079.table
  base := (14239881405815476421237652168259173957213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-543010794342364790188316697898150204500000000000)
      constant := (11337141428887811236546908589911821281901830504906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55160092949116193761/12500000000000000000)
  centralHi := (441280743592929550089/100000000000000000000)
  directionLo := (2775627859661434313/625000000000000000)
  directionHi := (444100457545829490081/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree080.table
  base := (29974735200276170895347383354478190225863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-549265132220180882074788239658696357000000000000)
      constant := (11605853041332615578587951669248714389434972623103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree080.table
  base := (14987366786551573659022503092760871503157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-549880383597665127009761584969851357000000000000)
      constant := (11631381307044313392305836180911535862067105711034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2775627859661434313/625000000000000000)
  centralHi := (444100457545829490081/100000000000000000000)
  directionLo := (446902380972513244877/100000000000000000000)
  directionHi := (223451190486256622439/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree081.table
  base := (31500108809997146202889336172210169971171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-6865765812756329207833900739679112000000000000)
      constant := (146953505961998036752359723386383524343092658571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree081.table
  base := (31500107418685379290274927408243538602469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-6873456454974882269521067556068549500000000000)
      constant := (147276595826141751674926661627905828297724331069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446902380972513244877/100000000000000000000)
  centralHi := (223451190486256622439/50000000000000000000)
  directionLo := (17987473856898867409/4000000000000000000)
  directionHi := (224843423211235842613/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree082.table
  base := (33055885102031330684871970645749650109487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-562988929446344449594303680169319787000000000000)
      constant := (12204390025278442867041998313762310026024498030247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree082.table
  base := (33055883912573680551614145001793628265603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-563619562108265800652651359113253662000000000000)
      constant := (12231210290351450561136994757300438321193927078043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17987473856898867409/4000000000000000000)
  centralHi := (224843423211235842613/50000000000000000000)
  directionLo := (452454176212214779673/100000000000000000000)
  directionHi := (226227088106107389837/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree083.table
  base := (17321031851780783101923419711921627991671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-569850828059426233354061400424631502000000000000)
      constant := (12509321165702672881764205507670846413369007409502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree083.table
  base := (34642062686823888686737737573694032394341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-570489151363566137474096246184954814500000000000)
      constant := (12536799389681758757518152150141611717100129859021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452454176212214779673/100000000000000000000)
  centralHi := (226227088106107389837/50000000000000000000)
  directionLo := (455204682860754596713/100000000000000000000)
  directionHi := (227602341430377298357/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree084.table
  base := (36258644299762941023576391473177960940131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-64079191852500890790424346742215913000000000000)
      constant := (1424225266879414711604790882080934220474077863779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree084.table
  base := (4532330428848861686871290832204158107813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-64150971179874052699504570361850663000000000000)
      constant := (1427352395295430645727937203339143168107754480936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455204682860754596713/100000000000000000000)
  centralHi := (227602341430377298357/50000000000000000000)
  directionLo := (5724233368769328551/1250000000000000000)
  directionHi := (457938669501546284081/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree085.table
  base := (4738203328098449465017763635970159965761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-583574625285589800873576840935254932000000000000)
      constant := (13130508731989489212169758715418886570609651456328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree085.table
  base := (37905625882211195049697024171645995445647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-584228329874166811116986020328357119500000000000)
      constant := (13159326792383625571524759690669790327323864283207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5724233368769328551/1250000000000000000)
  centralHi := (457938669501546284081/100000000000000000000)
  directionLo := (115164107568106018793/25000000000000000000)
  directionHi := (460656430272424075173/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree086.table
  base := (39583010454150781638805827281244865349011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-590436523898671584633334561190566647000000000000)
      constant := (13446765154301341262771065856018775358272421525291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree086.table
  base := (19791504909836537574205754553472706462929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-591097919129467147938430907400058272000000000000)
      constant := (13476265092252659286897323056029086633677255115698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115164107568106018793/25000000000000000000)
  centralHi := (460656430272424075173/100000000000000000000)
  directionLo := (463358250684952162327/100000000000000000000)
  directionHi := (57919781335619020291/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree087.table
  base := (41290795598300381486404087735718761079639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-66366491390194818710343586827319818000000000000)
      constant := (1529644074164183388928758305247181937321027256151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree087.table
  base := (41290795056258469824970205988834425188607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-66440834264974164973319532719084380500000000000)
      constant := (1532998495101379260989056842339788050969704889663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463358250684952162327/100000000000000000000)
  centralHi := (57919781335619020291/12500000000000000000)
  directionLo := (233022203987251630167/50000000000000000000)
  directionHi := (93208881594900652067/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree088.table
  base := (43028981897185951310146119454788930930833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-604160321124835152152850001701190077000000000000)
      constant := (14090603270359414676007336123890734323345939483673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree088.table
  base := (43028981434174225975211053269690867303553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-604837097640067821581320681543460577000000000000)
      constant := (14121490882220231637403444676138871299952200281993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233022203987251630167/50000000000000000000)
  centralHi := (93208881594900652067/20000000000000000000)
  directionLo := (468715171432279867501/100000000000000000000)
  directionHi := (234357585716139933751/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree089.table
  base := (22398784607835965894760723251250823942307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-611022219737916935912607721956501792000000000000)
      constant := (14418184961968052204472750464225899889562622473334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree089.table
  base := (1119939220505469830247587288664426018301/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-611706686895368158402765568615161729500000000000)
      constant := (14449778370211537656088966640735678469200418751240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468715171432279867501/100000000000000000000)
  centralHi := (234357585716139933751/50000000000000000000)
  directionLo := (471370802720403729847/100000000000000000000)
  directionHi := (58921350340050466231/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree090.table
  base := (4659655743966382212941570174947156411273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-7628198991987638514473647434713747000000000000)
      constant := (182093107919473455877071138096736612303242174730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree090.table
  base := (46596557101954356143621816623133507051733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-7636744150008253027459388341813122000000000000)
      constant := (182491961963853272853864315567888355851431981933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471370802720403729847/100000000000000000000)
  centralHi := (58921350340050466231/12500000000000000000)
  directionLo := (237005778085558517163/50000000000000000000)
  directionHi := (474011556171117034327/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree091.table
  base := (12106486618209125619199394775655554639961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-3696721993870298836876468416965238000000000000)
      constant := (89258423717099238553129717711490142130570755556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree091.table
  base := (24212973092237319624879943303572261637163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-3700863108911058177784942856559550500000000000)
      constant := (89453861113104745453366213407887112505906594774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237005778085558517163/50000000000000000000)
  centralHi := (474011556171117034327/100000000000000000000)
  directionLo := (476637679071063691051/100000000000000000000)
  directionHi := (119159419767765922763/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree092.table
  base := (1005714724677422278915181517024653834471/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-1193965813945486365202043256564153000000000000)
      constant := (29156106921581186013643188690107317817003675950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree092.table
  base := (3142858499229731005838986914754878420573/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-1195303316940017332451985311588403000000000000)
      constant := (29219922867219710947681108058621653491187580752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476637679071063691051/100000000000000000000)
  centralHi := (119159419767765922763/25000000000000000000)
  directionLo := (95849882386310015469/20000000000000000000)
  directionHi := (239624705965775038673/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree093.table
  base := (52175926654121451631189976050402698403963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-70941090465582674550182066997527628000000000000)
      constant := (1751806955662253110523919258404398272197614265467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree093.table
  base := (13043981610987854223308167052079886786529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-71020560435174389520949457433551815500000000000)
      constant := (1755639880501791341201163799682962512212814248644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95849882386310015469/20000000000000000000)
  centralHi := (239624705965775038673/50000000000000000000)
  directionLo := (60230873593202654847/12500000000000000000)
  directionHi := (481846988745621238777/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree094.table
  base := (54096517675643111463501576960160773756531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-645331712803325854711396323233060367000000000000)
      constant := (16112719726101659794846752550254122690603217862411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree094.table
  base := (27048258748123833231576116610002389884641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-646054633171869842509990003973667492000000000000)
      constant := (16147961710972230484159295420170648971545939986642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60230873593202654847/12500000000000000000)
  centralHi := (481846988745621238777/100000000000000000000)
  directionLo := (242215318616365131337/50000000000000000000)
  directionHi := (19377225489309210507/4000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree095.table
  base := (14011877312382251946758525252043992893337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-652193611416407638471154043488372082000000000000)
      constant := (16462951936586433070070851669156125174992439648388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree095.table
  base := (14011877274104811952530644303916695080057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-652924222427170179331434891045368644500000000000)
      constant := (16498947555778909802103269373140810355848229977668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242215318616365131337/50000000000000000000)
  centralHi := (19377225489309210507/4000000000000000000)
  directionLo := (487000579071724898243/100000000000000000000)
  directionHi := (121750144767931224561/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree096.table
  base := (29014450667251820951149145493423956842457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-73228390003276602470101307082631533000000000000)
      constant := (1868551025790633564532188279619182300982104968626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree096.table
  base := (2901445060192128492389015440651332552441/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-73310423520274501794764419790785533000000000000)
      constant := (1872635162071331673515414022029645598673740011380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487000579071724898243/100000000000000000000)
  centralHi := (121750144767931224561/25000000000000000000)
  directionLo := (244778515061413040091/50000000000000000000)
  directionHi := (489557030122826080183/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree097.table
  base := (60040693895735903141891800045499534769907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-665917408642571205990669483998995512000000000000)
      constant := (17174741612437238000896389678429081486482620912267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree097.table
  base := (2401627751369769191649697093251663065493/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-666663400937770852974324665188770949500000000000)
      constant := (17212268419313266067693588558895700831132357878325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244778515061413040091/50000000000000000000)
  centralHi := (489557030122826080183/100000000000000000000)
  directionLo := (492100200639227446719/100000000000000000000)
  directionHi := (1537813126997585771/312500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree098.table
  base := (1940090215744888595032620576656928101873/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-672779307255652989750427204254307227000000000000)
      constant := (17536299077338218363949072456362245593778540605216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree098.table
  base := (15520721702177978011444112926690283038121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-673532990193071189795769552260472102000000000000)
      constant := (17574603437583384836222597493321835268208201988804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492100200639227446719/100000000000000000000)
  centralHi := (1537813126997585771/312500000000000000)
  directionLo := (494630295468902891447/100000000000000000000)
  directionHi := (61828786933612861431/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree099.table
  base := (6415548033401087860443393490707328092239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-8390632171218947821113394129748382000000000000)
      constant := (221007797859741917165135186839954623575242588390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree099.table
  base := (64155480252859233306453508607086071889447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-8400031845041623785397709127557694500000000000)
      constant := (221490389052787010319313498258735801866113451247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494630295468902891447/100000000000000000000)
  centralHi := (61828786933612861431/12500000000000000000)
  directionLo := (497147514247170347219/100000000000000000000)
  directionHi := (24857375712358517361/5000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree100.table
  base := (66258474165344763561799443509758249469089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-686503104481816557269942644764930657000000000000)
      constant := (18270739260188417041089851330660836190623668080809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree100.table
  base := (33129237048060289019731888245328457485883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-687272168703671863438659326403874407000000000000)
      constant := (18310622646241429552477587475496039114786659025446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497147514247170347219/100000000000000000000)
  centralHi := (24857375712358517361/5000000000000000000)
  directionLo := (249826025790262047347/50000000000000000000)
  directionHi := (99930410316104818939/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree101.table
  base := (68391868380199584377714600690945624014699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-693365003094898341029700365020242372000000000000)
      constant := (18643621977858454713387595407602564971273086529219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree101.table
  base := (6839186832115569608883468195303042006787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-694141757958972200260104213475575559500000000000)
      constant := (18684306836354860894022457416107771711421624315470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249826025790262047347/50000000000000000000)
  centralHi := (99930410316104818939/20000000000000000000)
  directionLo := (12553602430555366723/2500000000000000000)
  directionHi := (502144097222214668921/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree102.table
  base := (14111132592740555669276433156746443899519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-77802989078664458309939787252839343000000000000)
      constant := (2113364419949056547445982561857744900897740415355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree102.table
  base := (17638915728336745430296645850935328985739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-77890149690474726342394344505252968000000000000)
      constant := (2117974898167798749590582604492070410917045884204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12553602430555366723/2500000000000000000)
  centralHi := (502144097222214668921/100000000000000000000)
  directionLo := (252311918120012339561/50000000000000000000)
  directionHi := (504623836240024679123/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree103.table
  base := (72749857903317009330345361973047304675641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-707088800321061908549215805530865802000000000000)
      constant := (19400712665146790800538587640384678387097365464321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree103.table
  base := (14549971572075002246540559221055903899397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-707880936469572873902993987618977864500000000000)
      constant := (19443024387618202236673807398448955821204671434785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252311918120012339561/50000000000000000000)
  centralHi := (504623836240024679123/100000000000000000000)
  directionLo := (507091449176660354963/100000000000000000000)
  directionHi := (126772862294165088741/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree104.table
  base := (74974453188476429423977300087349678644613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-4224560348722743741473216128912293000000000000)
      constant := (117070536299395194953280131642441813380243022437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree104.table
  base := (74974453151860160501439928488040657394307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4370598)
      previous := (2185299)
      next := (2185299)
      square := (39186780042842677396763839818180000000000000)
      linear := (-4229293051626468702511472631305793000000000000)
      constant := (117325785494696671681845884834567383628688660643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507091449176660354963/100000000000000000000)
  centralHi := (126772862294165088741/25000000000000000000)
  directionLo := (995209203521781643/195312500000000000)
  directionHi := (509547112203152201217/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree105.table
  base := (3089177952411180277137902396819478300441/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-80090288616358386229859027337943248000000000000)
      constant := (2241433743092226677115903185348755528833488314225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree105.table
  base := (3861472438953000946102438316455735125977/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-80180012775574838616209306862486685500000000000)
      constant := (2246319351822609619855205558116366334257669559860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (995209203521781643/195312500000000000)
  centralHi := (509547112203152201217/100000000000000000000)
  directionLo := (51199099726563361321/10000000000000000000)
  directionHi := (511990997265633613211/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree106.table
  base := (79514844761229627319268804189516940436267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-727674496160307259828488966296800947000000000000)
      constant := (20564661824789260649711547814408060710347359191427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree106.table
  base := (39757422367306958172129245673471313632633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-728489704235473884367328648834081322000000000000)
      constant := (20609473640964147277028040581024820997619005698946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51199099726563361321/10000000000000000000)
  centralHi := (511990997265633613211/100000000000000000000)
  directionLo := (514423272225843523903/100000000000000000000)
  directionHi := (8037863628528805061/1562500000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree107.table
  base := (81830641035016040657299703335139534490891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-734536394773389043588246686552112662000000000000)
      constant := (20960195045429750438329556592062039317552131849571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree107.table
  base := (16366128202465446166411929883127059667333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-735359293490774221188773535905782474500000000000)
      constant := (21005856172240861372173730533101462034287416200865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514423272225843523903/100000000000000000000)
  centralHi := (8037863628528805061/1562500000000000000)
  directionLo := (516844100995677980281/100000000000000000000)
  directionHi := (258422050497838990141/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree108.table
  base := (84176837626328883232034091139951463505183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-9153065350450257127753140824783017000000000000)
      constant := (263697572218679730650925124667340344288826865383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree108.table
  base := (84176837606989286009451409616988860096171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-9163319540074994543336029913302267000000000000)
      constant := (264271873582665380866172358101220177081457783571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516844100995677980281/100000000000000000000)
  centralHi := (258422050497838990141/50000000000000000000)
  directionLo := (16226676364565495447/3125000000000000000)
  directionHi := (103850728733219170861/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree109.table
  base := (43276717265351488074527440513316845913223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-748260191999552611107762127062736092000000000000)
      constant := (21762586737606849374772160993860635592258564006526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree109.table
  base := (3462137380568784406992618361637800063/400000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-749098472001374894831663310049184779500000000000)
      constant := (21809970404797529608388425318126695957778457575000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16226676364565495447/3125000000000000000)
  centralHi := (103850728733219170861/20000000000000000000)
  directionLo := (521652056630665565727/100000000000000000000)
  directionHi := (16301626769708298929/3125000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree110.table
  base := (88960431744385926967020678186121629741373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-755122090612634394867519847318047807000000000000)
      constant := (22169445209083951135902716954456902577961187493413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree110.table
  base := (3558417269213525714927431791739938054617/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-755968061256675231653108197120885932000000000000)
      constant := (22217702106019113558995635803282162690029649194425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521652056630665565727/100000000000000000000)
  centralHi := (16301626769708298929/3125000000000000000)
  directionLo := (524039492704022624527/100000000000000000000)
  directionHi := (32752468294001414033/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree111.table
  base := (9139782926422675590481816559756498533167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-84664887691746242069697507508151058000000000000)
      constant := (2508897640457949522877809637309989427970229667030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree111.table
  base := (91397829252255661539479736144271052317709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-84759738945775063163839231576954120500000000000)
      constant := (2514357429315364128385752773969681665837424520781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524039492704022624527/100000000000000000000)
  centralHi := (32752468294001414033/6250000000000000000)
  directionLo := (263208050617745946173/50000000000000000000)
  directionHi := (526416101235491892347/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree112.table
  base := (11733203385947731933434798931807617245307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-768845887838797962387035287828671237000000000000)
      constant := (22994487402700489451318595077762936561497303837336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree112.table
  base := (23466406769345320215583214255054945102143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-769707239767275905295997971264288237000000000000)
      constant := (23044514678236258551061418229977767194652846375132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263208050617745946173/50000000000000000000)
  centralHi := (526416101235491892347/100000000000000000000)
  directionLo := (105756405643622725333/20000000000000000000)
  directionHi := (264391014109056813333/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree113.table
  base := (96363825212235588379541740012854543986747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-775707786451879746146793008083982952000000000000)
      constant := (23412671124804737876924509406698847117981192652307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree113.table
  base := (48181912601772183649531652761053751098709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-776576829022576242117442858335989389500000000000)
      constant := (23463595549197339144207272276460919680073185696058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105756405643622725333/20000000000000000000)
  centralHi := (264391014109056813333/50000000000000000000)
  directionLo := (132784354098324631747/25000000000000000000)
  directionHi := (531137416393298526989/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree114.table
  base := (98892423636333247655171452523042871949241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-86952187229440169989616747593254963000000000000)
      constant := (2648292214491206684146613951667786554156206851769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree114.table
  base := (395569694515714498964743749670300510627/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-87049602030875175437654193934187838000000000000)
      constant := (2654051052967596251238818666048411612576269960750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132784354098324631747/25000000000000000000)
  centralHi := (531137416393298526989/100000000000000000000)
  directionLo := (266741202675662037447/50000000000000000000)
  directionHi := (106696481070264814979/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree115.table
  base := (101451422358324456458660416419760876090933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-1492309231905563919974118050273358000000000000)
      constant := (45860801171148637557854499764632143820308781837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree115.table
  base := (50725711176008228272674081000878868752259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (1396278)
      previous := (698139)
      next := (698139)
      square := (12519028028809853459457635026980000000000000)
      linear := (-1493981110648727629036545619053670500000000000)
      constant := (45960503706537524110830252971667421121824346902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266741202675662037447/50000000000000000000)
  centralHi := (106696481070264814979/20000000000000000000)
  directionLo := (33488570726742023813/6250000000000000000)
  directionHi := (535817131627872381009/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree116.table
  base := (52020410688457692118892169960675790610827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-796293482291125097426066168849918097000000000000)
      constant := (24689872792145675959919872121464497264236564229574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree116.table
  base := (26010205342885501004988172732732371889889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-797185596788477252581777519551092847000000000000)
      constant := (24743536501338124432982893135997391291002261142436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33488570726742023813/6250000000000000000)
  centralHi := (535817131627872381009/100000000000000000000)
  directionLo := (107628345759359691861/20000000000000000000)
  directionHi := (269070864398399229653/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree117.table
  base := (10666062069102840799346143758356758280789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (53958)
      previous := (26979)
      next := (26979)
      square := (483787407936329350577331355780000000000000)
      linear := (-58671588933027020321851405442708000000000000)
      constant := (1835280652219825892781871359207521688805373810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree117.table
  base := (53330310343225755224196972190272559898053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (53958)
      previous := (26979)
      next := (26979)
      square := (483787407936329350577331355780000000000000)
      linear := (-58737320917800978114049412420395500000000000)
      constant := (1839268726600924686753489242866407571497140074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107628345759359691861/20000000000000000000)
  centralHi := (269070864398399229653/50000000000000000000)
  directionLo := (33778520472456705319/6250000000000000000)
  directionHi := (108091265511861457021/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree118.table
  base := (109310820299768060701599980664972057825203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-810017279517288664945581609360541527000000000000)
      constant := (25560215987805706819777438323733936815772108845643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree118.table
  base := (27327705073967467493865251684049098288789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-810924775299077926224667293694495152000000000000)
      constant := (25615745752057814004162568554400311035239092226036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33778520472456705319/6250000000000000000)
  centralHi := (108091265511861457021/20000000000000000000)
  directionLo := (27138052791485405243/5000000000000000000)
  directionHi := (542761055829708104861/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree119.table
  base := (13998927525299036115503543106170700398831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-816879178130370448705339329615853242000000000000)
      constant := (26001050210845832914505571491866118547746116869688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree119.table
  base := (111991420199072398212824474644921544522319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-817794364554378263046112180766196304500000000000)
      constant := (26057524962186144546335972066281755756727152114439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27138052791485405243/5000000000000000000)
  centralHi := (542761055829708104861/100000000000000000000)
  directionLo := (545056038817905204819/100000000000000000000)
  directionHi := (27252801940895260241/5000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree120.table
  base := (22940484079657638736907522134403536197439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-91526786304828025829455227763462773000000000000)
      constant := (2938406613039237403798255577583770359281425981755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree120.table
  base := (22940484079092202264666901092588336891783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-91629328201075399985284118648655273000000000000)
      constant := (2944787469868968738971733011287185868290803139235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545056038817905204819/100000000000000000000)
  centralHi := (27252801940895260241/5000000000000000000)
  directionLo := (68417674888596958381/12500000000000000000)
  directionHi := (547341399108775667049/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree121.table
  base := (117443820886951557092492608556660270267387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-830602975356534016224854770126476672000000000000)
      constant := (26894043907323966694538729784479057948533647880147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree121.table
  base := (117443820884544126920713722701861713927353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-831533543064978936689001954909598609500000000000)
      constant := (26952432551957976532881281377738502378735487129793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68417674888596958381/12500000000000000000)
  centralHi := (547341399108775667049/100000000000000000000)
  directionLo := (137404314184644126041/25000000000000000000)
  directionHi := (109923451347715300833/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree122.table
  base := (60107810833984782821692240410036560848049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-837464873969615799984612490381788387000000000000)
      constant := (27346203380755333714419415943296749238372981441138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree122.table
  base := (60107810832959853500437647761105442671439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-838403132320279273510446841981299762000000000000)
      constant := (27405560931595006842175152186869002980391129522318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137404314184644126041/25000000000000000000)
  centralHi := (109923451347715300833/20000000000000000000)
  directionLo := (275941864634257965099/50000000000000000000)
  directionHi := (551883729268515930199/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree123.table
  base := (123017822741006232715400777534002189095287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-93814085842521953749374467848566678000000000000)
      constant := (3089126437516089405898694403665344896053269777783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree123.table
  base := (984142581914087626947941674472347824741/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-93919191286175512259099081005888990500000000000)
      constant := (3095830263081049230633879809399535874192753908625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275941864634257965099/50000000000000000000)
  centralHi := (551883729268515930199/100000000000000000000)
  directionLo := (554140931855616359579/100000000000000000000)
  directionHi := (27707046592780817979/5000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree124.table
  base := (62925212052895050066848867319069312208247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-851188671195779367504127930892411817000000000000)
      constant := (28261847577990413751329805058141913049578177387614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree124.table
  base := (125850424104304242225646951628662413125897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-852142310830879947153336616124702067000000000000)
      constant := (28323166860359376206746801302841580883065333733457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554140931855616359579/100000000000000000000)
  centralHi := (27707046592780817979/5000000000000000000)
  directionLo := (556388977320989996793/100000000000000000000)
  directionHi := (278194488660494998397/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree125.table
  base := (1029707406096830912019682398625821898103/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-858050569808861151263885651147723532000000000000)
      constant := (28725332301790587407111311537982909633999601317875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree125.table
  base := (64356712880419474466866069256037019329919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-859011900086180283974781503196403219500000000000)
      constant := (28787644409483281000982204866356604907876607340078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556388977320989996793/100000000000000000000)
  centralHi := (278194488660494998397/50000000000000000000)
  directionLo := (4364281064184699657/781250000000000000)
  directionHi := (558627976215641556097/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree126.table
  base := (8225426731860976573623466766818394113109/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-10677931708912875741032634214852287000000000000)
      constant := (360402371716593590321600679982027954533696923344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree126.table
  base := (65803413854349434145311930284934430230649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (9118902)
      previous := (4559451)
      next := (4559451)
      square := (81760071941239660247568999126820000000000000)
      linear := (-10689894930141736059212671484791412000000000000)
      constant := (361184012532098196130837579072978573931600502498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4364281064184699657/781250000000000000)
  centralHi := (558627976215641556097/100000000000000000000)
  directionLo := (140214509220976676533/25000000000000000000)
  directionHi := (560858036883906706133/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree127.table
  base := (134530629948671511352286966887062807900577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-871774367035024718783401091658346962000000000000)
      constant := (29663626999749924544370344179532144205406178234537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree127.table
  base := (26906125989550996308117219739735791836003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-872751078596780957617671277339805524500000000000)
      constant := (29727948677208460576725412395152883800829979202215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140214509220976676533/25000000000000000000)
  centralHi := (560858036883906706133/100000000000000000000)
  directionLo := (563079265524629242943/100000000000000000000)
  directionHi := (8798113523822331921/1562500000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree128.table
  base := (27496966495737891413934456176755789626711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-878636265648106502543158811913658677000000000000)
      constant := (30138436973907379487015007908762047837109123994955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree128.table
  base := (137484832477909360070238362779171930534207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (738631062)
      previous := (369315531)
      next := (369315531)
      square := (6622565827240412480053088929272420000000000000)
      linear := (-879620667852081294439116164411506677000000000000)
      constant := (30203775395808091923171759172111629506696779840567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell096.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563079265524629242943/100000000000000000000)
  centralHi := (8798113523822331921/1562500000000000000)
  directionLo := (282645883125087366541/50000000000000000000)
  directionHi := (565291766250174733083/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree129.table
  base := (28093887059950792246622014392848590235363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-98388684917909809589212948018774488000000000000)
      constant := (3401891336835099878247120787597351327140925940335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree129.table
  base := (70234717649545014225560859963238348055227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (82070118)
      previous := (41035059)
      next := (41035059)
      square := (735840647471156942228120992141380000000000000)
      linear := (-98498917456375736806729005720356425500000000000)
      constant := (3409265018988702968582136890446825833808861282486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell096.Kernel129
