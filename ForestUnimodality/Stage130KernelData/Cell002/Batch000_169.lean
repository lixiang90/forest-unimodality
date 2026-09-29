import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell002.Parameters
import ForestUnimodality.BinomialMassData.Q37_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_140.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_140.Batch100_149
import ForestUnimodality.BinomialMassData.Q37_140.Batch150_199
import ForestUnimodality.BinomialMassData.Q19_70.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_70.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_70.Batch100_149
import ForestUnimodality.BinomialMassData.Q19_70.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree000.table
  base := (539156991740442486204187839/100000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (1495686923470637350042089500000000000000)
      constant := (377409894218309740342931487300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree000.table
  base := (539156991740442486204187839/100000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (747843461735318675021044750000000000000)
      constant := (188704947109154870171465743650000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree001.table
  base := (20334347717928900906636612006994209183673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (6417868688881811160829027170000000000000)
      constant := (1990534490447505424255346636736182499999954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree001.table
  base := (40314837051022631325977508112045561224489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (6308356803059847639492119080000000000000)
      constant := (1973149978785253707310712553447232499999961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (28071884069766799937/100000000000000000000)
  directionHi := (14035942034883399969/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree002.table
  base := (1919321452374520462108601195871941007653/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (2365928913469160871363427840000000000000)
      constant := (1501355716640357942108133708916601749999952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree002.table
  base := (7545436105881540717360521643972044642857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (1073452570912616914344805830000000000000)
      constant := (737740470101274745942040403073260374999986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/100000000000000000000)
  centralHi := (14035942034883399969/50000000000000000000)
  directionLo := (7939927834565888721/20000000000000000000)
  directionHi := (19849819586414721803/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree003.table
  base := (11593578313426941642611911825071666961751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-1686010861943489418102171490000000000000)
      constant := (1132688526380622574206062492763773362251598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree003.table
  base := (22595707661293371796668205834167460821677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-2014546519409379982112895760000000000000)
      constant := (1103747175897243434867553809787205580262173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7939927834565888721/20000000000000000000)
  centralHi := (19849819586414721803/50000000000000000000)
  directionLo := (24310964736509743783/50000000000000000000)
  directionHi := (48621929473019487567/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree004.table
  base := (4368747817353902044557777115926221058711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-5737950637356139707567770820000000000000)
      constant := (853773447349983116383597262433539327507356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree004.table
  base := (8441594374442272782664791403268034082279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-3087999090321996896457701590000000000000)
      constant := (412472661556394810843571846716133670031671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24310964736509743783/50000000000000000000)
  centralHi := (48621929473019487567/100000000000000000000)
  directionLo := (28071884069766799937/50000000000000000000)
  directionHi := (449150145116268799/800000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree005.table
  base := (1310868186709217978813357384394858851083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-9789890412768789997033370150000000000000)
      constant := (641876179917758776694068931122230837030670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree005.table
  base := (12551122639346646813524153135960301031239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-10337449841878607603717910600000000000000)
      constant := (614915194548489221609649303587054750530711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/50000000000000000000)
  centralHi := (449150145116268799/800000000000000000)
  directionLo := (62770641036492013613/100000000000000000000)
  directionHi := (31385320518246006807/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree006.table
  base := (9765547761542136259340384298693505269051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-13841830188181440286498969480000000000000)
      constant := (481185371825217924213526559712981758183499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree006.table
  base := (9258756523332909533426202154237599912371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-14498901503113221414520418020000000000000)
      constant := (456959902546350700251610621509642395706179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62770641036492013613/100000000000000000000)
  centralHi := (31385320518246006807/50000000000000000000)
  directionLo := (17190448022373068389/25000000000000000000)
  directionHi := (68761792089492273557/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree007.table
  base := (7184981684015386147892850144078710065799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-2556252851942012939423509830000000000000)
      constant := (51275895271943725455427764813800970460593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree007.table
  base := (168365292719308346644066334672656596977/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-1332882368881988230380208960000000000000)
      constant := (24126927942492504607760492853671923576780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17190448022373068389/25000000000000000000)
  centralHi := (68761792089492273557/100000000000000000000)
  directionLo := (37135612040819352983/50000000000000000000)
  directionHi := (74271224081638705967/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree008.table
  base := (5169249104403101155027478952707632097707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-21945709739006740865430168140000000000000)
      constant := (265424873177590651978061184130673972787643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree008.table
  base := (1193679108620578179201717656697849175953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-11410902412791224518062716430000000000000)
      constant := (123685922098087283394076482380389219243394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37135612040819352983/50000000000000000000)
  centralHi := (74271224081638705967/100000000000000000000)
  directionLo := (7939927834565888721/10000000000000000000)
  directionHi := (79399278345658887211/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree009.table
  base := (715768300412742955770812579191630510467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-25997649514419391154895767470000000000000)
      constant := (193830273135734886991106867412699475064415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree009.table
  base := (323625211030764253926357729125020287569/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-13491628243408531423463970140000000000000)
      constant := (89373175316292116636330131694129970454405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7939927834565888721/10000000000000000000)
  centralHi := (79399278345658887211/100000000000000000000)
  directionLo := (84215652209300399811/100000000000000000000)
  directionHi := (21053913052325099953/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree010.table
  base := (2310000734464480228881272017277286285653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-30049589289832041444361366800000000000000)
      constant := (139063317793934190493056235671587027996997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree010.table
  base := (2013953662484905123356981332701892954051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-31144708148051676657730447700000000000000)
      constant := (126742521889716571683154985502392754748499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84215652209300399811/100000000000000000000)
  centralHi := (21053913052325099953/25000000000000000000)
  directionLo := (44385545936330078969/50000000000000000000)
  directionHi := (88771091872660157939/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree011.table
  base := (321357861912304971538172017450249433297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-34101529065244691733826966130000000000000)
      constant := (97336534808335859155044794810998888926212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree011.table
  base := (128761364036457061371287448762120372633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-17653079904643145234266477560000000000000)
      constant := (43775789605085913545957378105875593036068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44385545936330078969/50000000000000000000)
  centralHi := (88771091872660157939/100000000000000000000)
  directionLo := (5818994163610712597/6250000000000000000)
  directionHi := (93103906617771401553/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree012.table
  base := (89486396121361813833304065262574244567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-38153468840657342023292565460000000000000)
      constant := (65822542789394783583484799197330689918915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree012.table
  base := (56782852880885405016590638034560471059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-19733805735260452139667731270000000000000)
      constant := (29177216315968301709559134731386926163782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5818994163610712597/6250000000000000000)
  centralHi := (93103906617771401553/100000000000000000000)
  directionLo := (97243858946038975133/100000000000000000000)
  directionHi := (48621929473019487567/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree013.table
  base := (-30897614754255891897629289560740752351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-42205408616069992312758164790000000000000)
      constant := (42405362419917513036289896768939625078408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree013.table
  base := (-27351780833125474087502629038151410953/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-21814531565877759045068984980000000000000)
      constant := (18529301566496531979275061683544646906424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97243858946038975133/100000000000000000000)
  centralHi := (48621929473019487567/50000000000000000000)
  directionLo := (101214617412424928111/100000000000000000000)
  directionHi := (6325913588276558007/6250000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree014.table
  base := (-830821333940158952914219277675320260291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-6608192627354663228889109160000000000000)
      constant := (3642386214604335205467451427272758177963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree014.table
  base := (-39839684053313833795711127057745462341/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-6827216398998590271562925340000000000000)
      constant := (3157961294173189636640140860894544090325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101214617412424928111/100000000000000000000)
  centralHi := (6325913588276558007/6250000000000000000)
  directionLo := (52517686195152339567/50000000000000000000)
  directionHi := (21007074478060935827/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree015.table
  base := (-1327904455302969124710149869992711013909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-50309288166895292891689363450000000000000)
      constant := (13900221814952589496252938539107160318459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree015.table
  base := (-1471737702489160881413697521730481450931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-51951966454224745711742984800000000000000)
      constant := (12330674200389195485820122260206408904381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52517686195152339567/50000000000000000000)
  centralHi := (21007074478060935827/20000000000000000000)
  directionLo := (54360969749436050507/50000000000000000000)
  directionHi := (21744387899774420203/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree016.table
  base := (-1756894441259000319570422006379556752793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-54361227942307943181154962780000000000000)
      constant := (6711173560394631429154032679401719113143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree016.table
  base := (-941362165221914924526290087343377246141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-28056709057729679761272746110000000000000)
      constant := (3429172953962343748084154216174514939091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54360969749436050507/50000000000000000000)
  centralHi := (21744387899774420203/20000000000000000000)
  directionLo := (28071884069766799937/25000000000000000000)
  directionHi := (112287536279067199749/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree017.table
  base := (-266477409164693750817329997596116956669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-58413167717720593470620562110000000000000)
      constant := (3242187644600896253838832009072152985752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree017.table
  base := (-1121217556414061036318421261433015351357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-30137434888346986666673999820000000000000)
      constant := (2514035463943303285491070776282247783507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/25000000000000000000)
  centralHi := (112287536279067199749/100000000000000000000)
  directionLo := (115743343129742280607/100000000000000000000)
  directionHi := (3616979472804446269/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree018.table
  base := (-2463392276473194019929993202011908442079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-62465107493133243760086161440000000000000)
      constant := (2968311142837168088863055494416486338129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree018.table
  base := (-640277387353695466828079640173545413657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-32218160718964293572075253530000000000000)
      constant := (3169056885705240634057877946992549461614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115743343129742280607/100000000000000000000)
  centralHi := (3616979472804446269/3125000000000000000)
  directionLo := (23819783503697666163/20000000000000000000)
  directionHi := (1860920586226380169/1562500000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree019.table
  base := (-344980413711926800815875520300948429487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-66517047268545894049551760770000000000000)
      constant := (5486280965598826641883101012778215641096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree019.table
  base := (-1423287611572941967507399838804752617679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-34298886549581600477476507240000000000000)
      constant := (5202461437167325596357686687067121733729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23819783503697666163/20000000000000000000)
  centralHi := (1860920586226380169/1562500000000000000)
  directionLo := (122362505814902767779/100000000000000000000)
  directionHi := (6118125290745138389/5000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree020.table
  base := (-1513767783620703407261069783187752234973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-70568987043958544339017360100000000000000)
      constant := (10484300594283285151468100047600280972646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree020.table
  base := (-1552429817715344487791214987183226004527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-36379612380198907382877760950000000000000)
      constant := (8466575333802671026355966528021925778177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122362505814902767779/100000000000000000000)
  centralHi := (6118125290745138389/5000000000000000000)
  directionLo := (125541282072984027227/100000000000000000000)
  directionHi := (31385320518246006807/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree021.table
  base := (-1635711992510827535333011888555903555701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-10660132402767313518354708490000000000000)
      constant := (2531368309896690872405351257467350220186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree021.table
  base := (-1670320546595524413275212874189186538131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-5494334030116602041182716380000000000000)
      constant := (1835254293717986700634274026175694233083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125541282072984027227/100000000000000000000)
  centralHi := (31385320518246006807/25000000000000000000)
  directionLo := (128641533649731367493/100000000000000000000)
  directionHi := (64320766824865683747/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree022.table
  base := (-3495396544655575008561756858786444575787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-78672866594783844917948558760000000000000)
      constant := (27001602591228103661439274132464215786437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree022.table
  base := (-1778790845114182747779290455408392013327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-40541064041433521193680268370000000000000)
      constant := (18253354305702684043434590828988791346977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128641533649731367493/100000000000000000000)
  centralHi := (64320766824865683747/50000000000000000000)
  directionLo := (1053350459590163783/800000000000000000)
  directionHi := (32917201862192618219/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree023.table
  base := (-925632233350478272621743832254826914299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-82724806370196495207414158090000000000000)
      constant := (38179665184458511163669356674803924797396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree023.table
  base := (-3758573832018841493259988923144097733769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-85243579744101656198163044160000000000000)
      constant := (49230868297332081864678389318939211045319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1053350459590163783/800000000000000000)
  centralHi := (32917201862192618219/25000000000000000000)
  directionLo := (67314013270283888557/50000000000000000000)
  directionHi := (26925605308113555423/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree024.table
  base := (-38952750336031604979289189037431396647/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-86776746145609145496879757420000000000000)
      constant := (51133525714185990720652960348586156429700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree024.table
  base := (-3945923291268743225304274140393093218853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-89405031405336270008965551580000000000000)
      constant := (63753056307224901265475865952738432276203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67314013270283888557/50000000000000000000)
  centralHi := (26925605308113555423/20000000000000000000)
  directionLo := (17190448022373068389/12500000000000000000)
  directionHi := (137523584178984547113/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree025.table
  base := (-1018902457646963364294421347270752422621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-90828685921021795786345356750000000000000)
      constant := (65766409899312267244175292653682525166284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree025.table
  base := (-4121485604825227171144435455111446405461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-93566483066570883819768059000000000000000)
      constant := (79982351335573158796064665824539126132411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17190448022373068389/12500000000000000000)
  centralHi := (137523584178984547113/100000000000000000000)
  directionLo := (28071884069766799937/20000000000000000000)
  directionHi := (70179710174416999843/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree026.table
  base := (-84902739806618410991105023151544849893/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-94880625696434446075810956080000000000000)
      constant := (81999738107065840249459511335715117762150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree026.table
  base := (-857353622597636751457329048777171803507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-97727934727805497630570566420000000000000)
      constant := (97844893707682223557642342481592908140785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/20000000000000000000)
  centralHi := (70179710174416999843/50000000000000000000)
  directionLo := (28627816931011070653/20000000000000000000)
  directionHi := (71569542327527676633/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree027.table
  base := (-4405170160276767092040923993161675162041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-98932565471847096365276555410000000000000)
      constant := (99769141612670849204519534981827917059991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree027.table
  base := (-2221503324560372065981379179781164828231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-50944693194520055720686536920000000000000)
      constant := (58640063794379334643424004067222923416681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28627816931011070653/20000000000000000000)
  centralHi := (71569542327527676633/50000000000000000000)
  directionLo := (145865788419058462699/100000000000000000000)
  directionHi := (1458657884190584627/1000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree028.table
  base := (-4556794688530353425678685443943914632691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-14712072178179963807820307820000000000000)
      constant := (17003062622712033914028609676392597571163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree028.table
  base := (-4591223481861102339791434413379494728863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-15150119721467817893167940180000000000000)
      constant := (19748280259361569685338191690343536897959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145865788419058462699/100000000000000000000)
  centralHi := (1458657884190584627/1000000000000000000)
  directionLo := (37135612040819352983/25000000000000000000)
  directionHi := (148542448163277411933/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree029.table
  base := (-470091471709692254466404562600074178157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-107036445022672396944207754070000000000000)
      constant := (139712325387749098114921713906713652703070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree029.table
  base := (-2366135677156743040840424216902764387071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-55106144855754669531489044340000000000000)
      constant := (80338305987946010872349883590264545033521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37135612040819352983/25000000000000000000)
  centralHi := (148542448163277411933/100000000000000000000)
  directionLo := (15117172216246788529/10000000000000000000)
  directionHi := (151171722162467885291/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree030.table
  base := (-4838289321202615951415713147052708535301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-111088384798085047233673353400000000000000)
      constant := (161804608012884497736167151719417281770251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree030.table
  base := (-4866867179359682234711836385415113624663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-114373741372743952873780596100000000000000)
      constant := (184560949338634214151884321914659432391513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15117172216246788529/10000000000000000000)
  centralHi := (151171722162467885291/100000000000000000000)
  directionLo := (153756041366812026281/100000000000000000000)
  directionHi := (76878020683406013141/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree031.table
  base := (-993912083808755707187870209234008319419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-115140324573497697523138952730000000000000)
      constant := (185266832242769536651659092258417961742345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree031.table
  base := (-199824720401688394707583272146589183777/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-118535193033978566684583103520000000000000)
      constant := (209861228304674130647467012797428249873175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153756041366812026281/100000000000000000000)
  centralHi := (76878020683406013141/50000000000000000000)
  directionLo := (156297635721143389513/100000000000000000000)
  directionHi := (78148817860571694757/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree032.table
  base := (-2547637238133506859294667978749503482437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-119192264348910347812604552060000000000000)
      constant := (210072221260720647264033080450548658721174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree032.table
  base := (-1279760303927875953258500899746293244031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-61348322347606590247692805470000000000000)
      constant := (118276048887920232221435906608863262084962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156297635721143389513/100000000000000000000)
  centralHi := (78148817860571694757/50000000000000000000)
  directionLo := (158798556691317774421/100000000000000000000)
  directionHi := (79399278345658887211/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree033.table
  base := (-1043179902402591113836295649974823655197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-123244204124322998102070151390000000000000)
      constant := (236197842128846760152314408222918204476735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree033.table
  base := (-1309395072592575786633522985590328405243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-63429048178223897153094059180000000000000)
      constant := (132305913272999500412219102398647816286186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158798556691317774421/100000000000000000000)
  centralHi := (79399278345658887211/50000000000000000000)
  directionLo := (80630348322564147507/50000000000000000000)
  directionHi := (32252139329025659003/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree034.table
  base := (-5331838530534697717496379208561144442429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-127296143899735648391535750720000000000000)
      constant := (263623947638746287457253612597503922320979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree034.table
  base := (-2675808674911673805918958697367248687883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-65509774008841204058495312890000000000000)
      constant := (147010845470358746176705365025004814293733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80630348322564147507/50000000000000000000)
  centralHi := (32252139329025659003/20000000000000000000)
  directionLo := (163685805608484327053/100000000000000000000)
  directionHi := (81842902804242163527/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree035.table
  base := (-108868804378292553201152086252404486403/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-18764011953592614097285907150000000000000)
      constant := (41761921731911748835599426442908429758950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree035.table
  base := (-68268538783495265009285563951905632293/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-9655785691351215851985223800000000000000)
      constant := (23197534731296837387979892580966422957960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163685805608484327053/100000000000000000000)
  centralHi := (81842902804242163527/50000000000000000000)
  directionLo := (16607550581866353663/10000000000000000000)
  directionHi := (166075505818663536631/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree036.table
  base := (-1110201508246222153619499506596798306837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-135400023450560948970466949380000000000000)
      constant := (322311510342914720137756671155784414824935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree036.table
  base := (-222698595222335157131456618789635096833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-139342451340151635738595640620000000000000)
      constant := (356829133188970198322522025254697006379575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16607550581866353663/10000000000000000000)
  centralHi := (166075505818663536631/100000000000000000000)
  directionLo := (84215652209300399811/50000000000000000000)
  directionHi := (168431304418600799623/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree037.table
  base := (-1413701175873204638472739195438395080179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-139451963225973599259932548710000000000000)
      constant := (353545176202918818221465673070824564284916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree037.table
  base := (-2834906582873245706641370065179339958311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-71751951500693124774699074020000000000000)
      constant := (195100179080552128351964922672712342042761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84215652209300399811/50000000000000000000)
  centralHi := (168431304418600799623/100000000000000000000)
  directionLo := (170754604574452985031/100000000000000000000)
  directionHi := (21344325571806623129/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree038.table
  base := (-5755062847627905841326689395563629677101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-143503903001386249549398148040000000000000)
      constant := (386023123748914949729776331350382145822051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree038.table
  base := (-5768746945969570793033501110842667383049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-147665354662620863360200655460000000000000)
      constant := (424868430756002903848159537776709298230599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170754604574452985031/100000000000000000000)
  centralHi := (21344325571806623129/12500000000000000000)
  directionLo := (21630839406174025123/12500000000000000000)
  directionHi := (34609343049878440197/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree039.table
  base := (-5851984746365008811407481687083464545667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-147555842776798899838863747370000000000000)
      constant := (419735417117199941793552116673660237262317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree039.table
  base := (-117289162911842947724852677269733954903/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-75913403161927738585501581440000000000000)
      constant := (230411973339902077069359132693075905243825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21630839406174025123/12500000000000000000)
  centralHi := (34609343049878440197/20000000000000000000)
  directionLo := (175308859826965546181/100000000000000000000)
  directionHi := (87654429913482773091/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree040.table
  base := (-5945748706285620551065351388171759551161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-151607782552211550128329346700000000000000)
      constant := (454673319285280633153124160179583781993111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree040.table
  base := (-1191423064587931373557038455612415474683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-155988257985090090981805670300000000000000)
      constant := (498058646574561659506728387574958208702665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175308859826965546181/100000000000000000000)
  centralHi := (87654429913482773091/50000000000000000000)
  directionLo := (44385545936330078969/25000000000000000000)
  directionHi := (177542183745320315877/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree041.table
  base := (-6036511837990425562917725503129470999751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-155659722327624200417794946030000000000000)
      constant := (490829131833723483180238538657405921012201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree041.table
  base := (-6046866779043726394177188991047518893769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-160149709646324704792608177720000000000000)
      constant := (536565263689725689282905285155671574205319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44385545936330078969/25000000000000000000)
  centralHi := (177542183745320315877/100000000000000000000)
  directionLo := (179747761277528873761/100000000000000000000)
  directionHi := (89873880638764436881/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree042.table
  base := (-1531103204004549281325364649910199385101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-22815951729005264386751506480000000000000)
      constant := (75456579958589800176627054041514417217172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree042.table
  base := (-61338431899330844113972894750299877279/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-11736511521968522757386477510000000000000)
      constant := (41166956778563467829592453569395042952350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179747761277528873761/100000000000000000000)
  centralHi := (89873880638764436881/50000000000000000000)
  directionLo := (181926601571924976841/100000000000000000000)
  directionHi := (90963300785962488421/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree043.table
  base := (-6209574223791877239278884416985774829573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-163763601878449500996726144690000000000000)
      constant := (566768096326771829269522325854447033350923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree043.table
  base := (-24872639398730782167876697319502879841/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-84236306484396966207106596280000000000000)
      constant := (308684695397688486998617616314544860973875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181926601571924976841/100000000000000000000)
  centralHi := (90963300785962488421/50000000000000000000)
  directionLo := (23009956756103555613/12500000000000000000)
  directionHi := (36815930809765688981/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree044.table
  base := (-251684182326251727810319240015861226201/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-167815541653862151286191744020000000000000)
      constant := (606539925338256630049646457132569997903775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree044.table
  base := (-6299918592637000573468292663707697085727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-172634064630028546225015699980000000000000)
      constant := (659656261493313363840530926830322842799377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23009956756103555613/12500000000000000000)
  centralHi := (36815930809765688981/20000000000000000000)
  directionLo := (37241562647108560621/20000000000000000000)
  directionHi := (93103906617771401553/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree045.table
  base := (-3186049976162210565259360080683930811141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-171867481429274801575657343350000000000000)
      constant := (647506836217147172850043153361724780508182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree045.table
  base := (-3189604724478728511073771920818213493991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-88397758145631580017909103700000000000000)
      constant := (351596797757893150423894681842407538794441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37241562647108560621/20000000000000000000)
  centralHi := (93103906617771401553/50000000000000000000)
  directionLo := (188311923109476040841/100000000000000000000)
  directionHi := (94155961554738020421/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree046.table
  base := (-806205708001487654079704603143249698161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-175919421204687451865122942680000000000000)
      constant := (689664651335377088479462203204846118320888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree046.table
  base := (-80701400959348918250871185896215184339/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-90478483976248886923310357410000000000000)
      constant := (373988744807853602493967479899418238695560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188311923109476040841/100000000000000000000)
  centralHi := (94155961554738020421/50000000000000000000)
  directionLo := (47598195252298985927/25000000000000000000)
  directionHi := (190392781009195943709/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree047.table
  base := (-6524817366284281536637111887608797350827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-179971360980100102154588542010000000000000)
      constant := (733009662712734523221806942763918929809477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree047.table
  base := (-6530697005628865114903288885349468421357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-185118419613732387657423222240000000000000)
      constant := (794004487841671810105209101730876047353507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47598195252298985927/25000000000000000000)
  centralHi := (190392781009195943709/100000000000000000000)
  directionLo := (192451141164821547097/100000000000000000000)
  directionHi := (96225570582410773549/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree048.table
  base := (-1319536454295808801469035579024055810277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-184023300755512752444054141340000000000000)
      constant := (777538576944682860800503777267106326482135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree048.table
  base := (-6603026720133315746687083511417997378413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-189279871274967001468225729660000000000000)
      constant := (841271528451562931957712665668518128457763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192451141164821547097/100000000000000000000)
  centralHi := (96225570582410773549/50000000000000000000)
  directionLo := (97243858946038975133/50000000000000000000)
  directionHi := (194487717892077950267/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree049.table
  base := (-6668300112982401044921846894893780181343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-26867891504417914676217105810000000000000)
      constant := (117606923870756813372530302342993538730599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree049.table
  base := (-1334631321243500342363921037768474466349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-27634474705171659325575462440000000000000)
      constant := (127110842504789284154559693729103393677785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97243858946038975133/50000000000000000000)
  centralHi := (194487717892077950267/100000000000000000000)
  directionLo := (196503188488367599559/100000000000000000000)
  directionHi := (4912579712209189989/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree050.table
  base := (-6736724005257371681740860173465187268739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-192127180306338053022985340000000000000000)
      constant := (870136730555891089057118637125205823831789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree050.table
  base := (-674113578017458557088406960948860248347/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-98801387298718114544915372250000000000000)
      constant := (469757594194596508004623552067529239154985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196503188488367599559/100000000000000000000)
  centralHi := (4912579712209189989/2500000000000000000)
  directionLo := (99249097932073609013/50000000000000000000)
  directionHi := (198498195864147218027/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree051.table
  base := (-6803001199049694794662772054344643841323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-196179120081750703312450939330000000000000)
      constant := (918201052039921842182556177587862451775173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree051.table
  base := (-6807007816052737576180425641317908497223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-201764226258670842900633251920000000000000)
      constant := (990487265890206670377002915232422483636073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99249097932073609013/50000000000000000000)
  centralHi := (198498195864147218027/100000000000000000000)
  directionLo := (200473350938591782611/100000000000000000000)
  directionHi := (50118337734647945653/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree052.table
  base := (-6867173745928302989514605029700086987369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-200231059857163353601916538660000000000000)
      constant := (967439371020512255298500635672695737618919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree052.table
  base := (-6870811385120127193805277752940540083871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-205925677919905456711435759340000000000000)
      constant := (1042690235144425648346451670433913535890321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200473350938591782611/100000000000000000000)
  centralHi := (50118337734647945653/25000000000000000000)
  directionLo := (202429234824849856223/100000000000000000000)
  directionHi := (6325913588276558007/3125000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree053.table
  base := (-6929279084087108735286833912182410031809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-204282999632576003891382137990000000000000)
      constant := (1017849853026160617424418745559811908441359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree053.table
  base := (-1733145204711397836592856033419909785357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-105043564790570035261119133380000000000000)
      constant := (548061206954938470354783129231348841035014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202429234824849856223/100000000000000000000)
  centralHi := (6325913588276558007/3125000000000000000)
  directionLo := (204366400827045522531/100000000000000000000)
  directionHi := (51091600206761380633/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree054.table
  base := (-3494675277761987663488184939602593657339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-208334939407988654180847737320000000000000)
      constant := (1069430864298971627105461859555945821580778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree054.table
  base := (-6992346605167912522768109226760860430733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-214248581242374684333040774180000000000000)
      constant := (1150782308277560205510773701600717838894083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204366400827045522531/100000000000000000000)
  centralHi := (51091600206761380633/25000000000000000000)
  directionLo := (206285376268476820669/100000000000000000000)
  directionHi := (20628537626847682067/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree055.table
  base := (-7047417863229579738157383483476560984211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-212386879183401304470313336650000000000000)
      constant := (1122180949392402112636495620578398511773661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree055.table
  base := (-7050135826427720554481400160362029185277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-218410032903609298143843281600000000000000)
      constant := (1206668591212784581007256710567260569921427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206285376268476820669/100000000000000000000)
  centralHi := (20628537626847682067/10000000000000000000)
  directionLo := (208186664168129383341/100000000000000000000)
  directionHi := (104093332084064691671/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree056.table
  base := (-7103507475793960878681984912003239560063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-30919831279830564965682705140000000000000)
      constant := (168014115906505738204966661351977323079559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree056.table
  base := (-7105972546172462234340760057753860384799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-31795926366406273136377969860000000000000)
      constant := (180540011943103596335767370331722977306407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208186664168129383341/100000000000000000000)
  centralHi := (104093332084064691671/50000000000000000000)
  directionLo := (210070744780609358269/100000000000000000000)
  directionHi := (21007074478060935827/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree057.table
  base := (-3578821492909404950175146564272671484649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-220490758734226605049244535310000000000000)
      constant := (1231183294120902925062069056988028194504398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree057.table
  base := (-7159878151069568611950018512874344250043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-226732936226078525765448296440000000000000)
      constant := (1322115737497677864109530696762157131747893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210070744780609358269/100000000000000000000)
  centralHi := (21007074478060935827/10000000000000000000)
  directionLo := (211938077012853782697/100000000000000000000)
  directionHi := (105969038506426891349/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree058.table
  base := (-7209845427668208952353665830028925755557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-224542698509639255338710134640000000000000)
      constant := (1287433367034650360208026376001582637977707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree058.table
  base := (-1802967913334901481131310736610812818483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-115447193943656569788125401930000000000000)
      constant := (690837310650917452330573360136140343788666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211938077012853782697/100000000000000000000)
  centralHi := (105969038506426891349/50000000000000000000)
  directionLo := (13361818733091216989/6250000000000000000)
  directionHi := (8551563989178378873/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree059.table
  base := (-7260133559368012026190982180638107332777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-228594638285051905628175733970000000000000)
      constant := (1344848110943515627289193507459482740693927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree059.table
  base := (-7261969958421648261362542754011539717731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-235055839548547753387053311280000000000000)
      constant := (1442455906647681665629710302470434553831181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13361818733091216989/6250000000000000000)
  centralHi := (8551563989178378873/4000000000000000000)
  directionLo := (21562423295714977463/10000000000000000000)
  directionHi := (215624232957149774631/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree060.table
  base := (-7308524112849814284349484244291774922889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-232646578060464555917641333300000000000000)
      constant := (1403426705982850563343695590229703028778439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree060.table
  base := (-7310188101985299162279537269291646990189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-239217291209782367197855818700000000000000)
      constant := (1504458856787407573564158096004709297480739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21562423295714977463/10000000000000000000)
  centralHi := (215624232957149774631/100000000000000000000)
  directionLo := (217443878997744202029/100000000000000000000)
  directionHi := (21744387899774420203/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree061.table
  base := (-7355032016210193313302850371223694235917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-236698517835877206207106932630000000000000)
      constant := (1463168420675922866634322385150788982440067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree061.table
  base := (-7356539459890293427822655518577125742717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-243378742871016981008658326120000000000000)
      constant := (1567682816303885623237715078586720838606867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217443878997744202029/100000000000000000000)
  centralHi := (21744387899774420203/10000000000000000000)
  directionLo := (219248423457985323577/100000000000000000000)
  directionHi := (109624211728992661789/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree062.table
  base := (-3699835295602188677313980269444688394981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-240750457611289856496572531960000000000000)
      constant := (1524072602256726353323806773327420537291862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree062.table
  base := (-7401035934251545673633300329325375575601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-247540194532251594819460833540000000000000)
      constant := (1632127201993484998483952511671056596795551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219248423457985323577/100000000000000000000)
  centralHi := (109624211728992661789/50000000000000000000)
  directionLo := (221038236203690505623/100000000000000000000)
  directionHi := (27629779525461313203/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree063.table
  base := (-3721225864401770404476256146554646037889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-34971771055243215255148304470000000000000)
      constant := (226591238295381925397341653573484955469554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree063.table
  base := (-1860922029595928308944715218017185379941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-17978689013820443473590238640000000000000)
      constant := (121270821055984820702540594707259404680826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221038236203690505623/100000000000000000000)
  centralHi := (27629779525461313203/12500000000000000000)
  directionLo := (111406836122458058949/50000000000000000000)
  directionHi := (222813672244916117899/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree064.table
  base := (-935423255663345764323755285542464538061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-248854337162115157075503730620000000000000)
      constant := (1649366097910109200529713494339353901080088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree064.table
  base := (-3742252721532873478400786525898281643463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-127931548927360411220532924190000000000000)
      constant := (882337616283312253003996480966984199470313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111406836122458058949/50000000000000000000)
  centralHi := (222813672244916117899/100000000000000000000)
  directionLo := (28071884069766799937/12500000000000000000)
  directionHi := (224575072558134399497/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree065.table
  base := (-7522483021204410838551047526335195015247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-252906276937527807364969329950000000000000)
      constant := (1713754427240006000785258177628325444252897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree065.table
  base := (-7523496306275095416145783545875690095047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-260024549515955436251868355800000000000000)
      constant := (1832778003841101066608453432577091185342697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/12500000000000000000)
  centralHi := (224575072558134399497/100000000000000000000)
  directionLo := (9052910594032640263/4000000000000000000)
  directionHi := (14145172803176000411/6250000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree066.table
  base := (-1889937781183172664004237435923215765761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-256958216712940457654434929280000000000000)
      constant := (1779303241113789310464135960376049709910844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree066.table
  base := (-7560668188287080114506899543749603198859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-264186001177190050062670863220000000000000)
      constant := (1902099442073726418102874785548269443255909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9052910594032640263/4000000000000000000)
  centralHi := (14145172803176000411/6250000000000000000)
  directionLo := (57014266068318475881/25000000000000000000)
  directionHi := (9122282570930956141/4000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree067.table
  base := (-1898799480458595262222185656817325683799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-261010156488353107943900528610000000000000)
      constant := (1846012168800263130953198151730554165975396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree067.table
  base := (-3798013876906185561829177288611674824621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-134173726419212331936736685320000000000000)
      constant := (986319610346838863487179388894527933593571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57014266068318475881/25000000000000000000)
  centralHi := (9122282570930956141/4000000000000000000)
  directionLo := (229778274082147747601/100000000000000000000)
  directionHi := (114889137041073873801/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree068.table
  base := (-3814415087021601954761172624616896642871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-265062096263765758233366127940000000000000)
      constant := (1913880878984275089527004717155544128998642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree068.table
  base := (-7629580942650187272850594603515553281649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-272508904499659277684275878060000000000000)
      constant := (2044397048650793270589633557395737889199199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229778274082147747601/100000000000000000000)
  centralHi := (114889137041073873801/50000000000000000000)
  directionLo := (46297337251896912243/20000000000000000000)
  directionHi := (3616979472804446269/1562500000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree069.table
  base := (-7660653925635973265357880547091587753013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-269114036039178408522831727270000000000000)
      constant := (1982909075496261298840989632713262200102363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree069.table
  base := (-1532266610032641892436679772924793834251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-276670356160893891495078385480000000000000)
      constant := (2117372666472301684843809941510425510608505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46297337251896912243/20000000000000000000)
  centralHi := (3616979472804446269/1562500000000000000)
  directionLo := (233182582090994663961/100000000000000000000)
  directionHi := (116591291045497331981/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree070.table
  base := (-7690674581243783858689480554151893593173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-39023710830655865544613903800000000000000)
      constant := (293299499072756873788962918395936744847789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree070.table
  base := (-7691288798729159979760778203901672456053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-40118829688875500757982984700000000000000)
      constant := (313080834680242082517113056972688292807629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233182582090994663961/100000000000000000000)
  centralHi := (116591291045497331981/50000000000000000000)
  directionLo := (46973246541345167033/20000000000000000000)
  directionHi := (117433116353362917583/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree071.table
  base := (-3859448487489384532762339321661302605867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-277217915590003709101762925930000000000000)
      constant := (2124442896151891007147887970057942344625034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree071.table
  base := (-7719452401190940869610727882452467926563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-284993259483363119116683400320000000000000)
      constant := (2266976371089669748760206161496829071598413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46973246541345167033/20000000000000000000)
  centralHi := (117433116353362917583/50000000000000000000)
  directionLo := (118268949793549278243/50000000000000000000)
  directionHi := (236537899587098556487/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree072.table
  base := (-968165679001744031992470574043621941939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-281269855365416359391228525260000000000000)
      constant := (2196948071490561825582694057462900198759912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree072.table
  base := (-7745827617209886835866945823601895033437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-289154711144597732927485907740000000000000)
      constant := (2343604067232821797762503031331507143361587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118268949793549278243/50000000000000000000)
  centralHi := (236537899587098556487/100000000000000000000)
  directionLo := (238197835036976661631/100000000000000000000)
  directionHi := (1860920586226380169/781250000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree073.table
  base := (-971245477931064062669846587501123207793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-285321795140829009680694124590000000000000)
      constant := (2270611829841450797327381010346309702545144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree073.table
  base := (-1942604450830782203645515014010146610539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-146658081402916173369144207580000000000000)
      constant := (1210724383360415654380051617453505632167178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238197835036976661631/100000000000000000000)
  centralHi := (1860920586226380169/781250000000000000)
  directionLo := (239846282630207078071/100000000000000000000)
  directionHi := (29980785328775884759/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree074.table
  base := (-974101951899711868582357250163424487017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-289373734916241659970159723920000000000000)
      constant := (2345434001374710910184968231992937601089336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree074.table
  base := (-3896612978707299889581145037015393231959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-148738807233533480274545461290000000000000)
      constant := (1250255161328692783028051008502245731634009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239846282630207078071/100000000000000000000)
  centralHi := (29980785328775884759/12500000000000000000)
  directionLo := (24148347762684634769/10000000000000000000)
  directionHi := (241483477626846347691/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree075.table
  base := (-7813883911564157697397682611052822338023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-293425674691654310259625323250000000000000)
      constant := (2421414433979511917277130278777161705436873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree075.table
  base := (-781425475822838203393787771775173653647/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-150819533064150787179946715000000000000000)
      constant := (1290394301892012268369158763727582454856485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24148347762684634769/10000000000000000000)
  centralHi := (241483477626846347691/100000000000000000000)
  directionLo := (30388705920637179729/12500000000000000000)
  directionHi := (243109647365097437833/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree076.table
  base := (-7833171494074491302493754284319997988051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-297477614467066960549090922580000000000000)
      constant := (2498552991361050881412860270700320098585501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree076.table
  base := (-391675330024081047064925278492714505617/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-152900258894768094085347968710000000000000)
      constant := (1331141746379804049024827659854569892247670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30388705920637179729/12500000000000000000)
  centralHi := (243109647365097437833/100000000000000000000)
  directionLo := (244725011629805535559/100000000000000000000)
  directionHi := (6118125290745138389/2500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree077.table
  base := (-785068085609986741664943667368898878929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-43075650606068515834079503130000000000000)
      constant := (368121364477734341658534626969427078474970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree077.table
  base := (-7850983626071000799291699574397957817329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-44280281350110114568785492120000000000000)
      constant := (392142126375885531340826660358214295278697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244725011629805535559/100000000000000000000)
  centralHi := (6118125290745138389/2500000000000000000)
  directionLo := (246329782999203897863/100000000000000000000)
  directionHi := (30791222874900487233/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree078.table
  base := (-314656569348892084009645520088528810949/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-305581494017892261128022121240000000000000)
      constant := (2656304004360761660909332630104552206587475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree078.table
  base := (-7866687751810820384458456602196110837461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-314123421112005415792300952260000000000000)
      constant := (2828922685474895760696202589180390568964411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246329782999203897863/100000000000000000000)
  centralHi := (30791222874900487233/12500000000000000000)
  directionLo := (247924167171458516329/100000000000000000000)
  directionHi := (24792416717145851633/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree079.table
  base := (-7880373633257009151216841969082254933983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-309633433793304911417487720570000000000000)
      constant := (2736916252101469213212179793395719508234833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree079.table
  base := (-985077586761395557234563943989071657177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-159142436386620014801551729840000000000000)
      constant := (1457033405593792534344047104846641955193308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247924167171458516329/100000000000000000000)
  centralHi := (24792416717145851633/10000000000000000000)
  directionLo := (49901672654486336661/20000000000000000000)
  directionHi := (124754181636215841653/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree080.table
  base := (-7892560855796024990336016011328458378273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-313685373568717561706953319900000000000000)
      constant := (2818686206312753263901069974244905539464623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree080.table
  base := (-986597998850099167469480410680411320497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-161223162217237321706952983550000000000000)
      constant := (1500213593206358693835586259906639381182588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49901672654486336661/20000000000000000000)
  centralHi := (124754181636215841653/50000000000000000000)
  directionLo := (50216512829193610891/20000000000000000000)
  directionHi := (31385320518246006807/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree081.table
  base := (-395148875954902716735962746702422307633/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-317737313344130211996418919230000000000000)
      constant := (2901613787724437281837094027202376138519660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree081.table
  base := (-3951589510410253031129834816166282086697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-163303888047854628612354237260000000000000)
      constant := (1544001871792566782534719922946352177751847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50216512829193610891/20000000000000000000)
  centralHi := (31385320518246006807/12500000000000000000)
  directionLo := (252646956627901199433/100000000000000000000)
  directionHi := (126323478313950599717/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree082.table
  base := (-7911625077113738218064521693888670804831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-321789253119542862285884518560000000000000)
      constant := (2985698925092939856369051767392455130563281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree082.table
  base := (-7911807021358293139673100914481064843513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-330769227756943871035510981940000000000000)
      constant := (3176796422081642065682925782158427822667863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252646956627901199433/100000000000000000000)
  centralHi := (126323478313950599717/50000000000000000000)
  directionLo := (127100860902441389443/50000000000000000000)
  directionHi := (254201721804882778887/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree083.table
  base := (-7918504837403773999895136419640981706947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-325841192894955512575350117890000000000000)
      constant := (3070941554347786816880300508504341896359597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree083.table
  base := (-7918669103367071188838345208709013304211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-334930679418178484846313489360000000000000)
      constant := (3266805167465549975286362132846258348093661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127100860902441389443/50000000000000000000)
  centralHi := (254201721804882778887/100000000000000000000)
  directionLo := (255747035259049374331/100000000000000000000)
  directionHi := (63936758814762343583/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree084.table
  base := (-3961808988339535739043114188598597413761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-47127590381481166123545102460000000000000)
      constant := (451048802547163369039279845215619636207346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree084.table
  base := (-3961883132629366232083802340239360719009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-24220866505672364189793999770000000000000)
      constant := (239859280772476755243825070846324474966937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255747035259049374331/100000000000000000000)
  centralHi := (63936758814762343583/25000000000000000000)
  directionLo := (257283067299462734987/100000000000000000000)
  directionHi := (64320766824865683747/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree085.table
  base := (-63415724437336102952168097730350406609/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-333945072445780813154281316550000000000000)
      constant := (3244899063613368426950249473570353759519875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree085.table
  base := (-3963549702552124911635876151566307768621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-171626791370323856233959252100000000000000)
      constant := (1725235334061769095020779791735750919337571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257283067299462734987/100000000000000000000)
  centralHi := (64320766824865683747/25000000000000000000)
  directionLo := (258809983181187000253/100000000000000000000)
  directionHi := (129404991590593500127/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree086.table
  base := (-3964274263242772927132187182216237091287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-337997012221193463443746915880000000000000)
      constant := (3333613844896681911509492744739808765053874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree086.table
  base := (-7928669331488300256243995594037977953163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-347415034401882326278721011620000000000000)
      constant := (3544127339771491652655820739364139080295013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258809983181187000253/100000000000000000000)
  centralHi := (129404991590593500127/50000000000000000000)
  directionLo := (130163971656400302253/50000000000000000000)
  directionHi := (260327943312800604507/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree087.table
  base := (-1585673550737393405180251876665394433997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-342048951996606113733212515210000000000000)
      constant := (3423485919464021503940526446493728363670735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree087.table
  base := (-991059596645999673311388976496495567033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-175788243031558470044761759520000000000000)
      constant := (1819499955024718196854701186923186868861532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130163971656400302253/50000000000000000000)
  centralHi := (260327943312800604507/100000000000000000000)
  directionLo := (261837103453080445989/100000000000000000000)
  directionHi := (26183710345308044599/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree088.table
  base := (-792642401411557232177766358016261115357/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-346100891772018764022678114540000000000000)
      constant := (3514515249201016703288896759780032053475070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree088.table
  base := (-1585304477533716164749589321807178292681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-355737937724351553900326026460000000000000)
      constant := (3735088346738635672325297049965241318293155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261837103453080445989/100000000000000000000)
  centralHi := (26183710345308044599/10000000000000000000)
  directionLo := (1053350459590163783/400000000000000000)
  directionHi := (263337614897540945751/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree089.table
  base := (-792271801070761717962734360283503857707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-350152831547431414312143713870000000000000)
      constant := (3606701799663790993105649608851833109723570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree089.table
  base := (-7922806768934055222039532843596608184167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-359899389385586167711128533880000000000000)
      constant := (3832392620735833260456278157660766198975817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1053350459590163783/400000000000000000)
  centralHi := (263337614897540945751/100000000000000000000)
  directionLo := (2118636997243682703/800000000000000000)
  directionHi := (66207406163865084469/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree090.table
  base := (-7917250379348025569673726777391965897743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-354204771322844064601609313200000000000000)
      constant := (3700045539693983098849837054732793671010593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree090.table
  base := (-7917330454137589674961946638974180554019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-364060841046820781521931041300000000000000)
      constant := (3930912705719543872516137966890265152853069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2118636997243682703/800000000000000000)
  centralHi := (66207406163865084469/25000000000000000000)
  directionLo := (133156637808990236907/50000000000000000000)
  directionHi := (53262655123596094763/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree091.table
  base := (-1582004339177164330087045705687702766689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-51179530156893816413010701790000000000000)
      constant := (542078063010712976679150963088180403165885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree091.table
  base := (-7910093929744788687530730944951042128879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-52603184672579342190390506960000000000000)
      constant := (575806939693278983965587839016342705097847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133156637808990236907/50000000000000000000)
  centralHi := (53262655123596094763/20000000000000000000)
  directionLo := (133894353358912096573/50000000000000000000)
  directionHi := (267788706717824193147/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree092.table
  base := (-7901032482399160018246790766672335073609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-362308650873669365180540511860000000000000)
      constant := (3890204478224984631597896515881055581393159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree092.table
  base := (-3950548818456280617686483741309289495477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-186191872184645004571768028070000000000000)
      constant := (2065800107759685883189740935999844814721627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133894353358912096573/50000000000000000000)
  centralHi := (267788706717824193147/100000000000000000000)
  directionLo := (269256053081135554229/100000000000000000000)
  directionHi := (26925605308113555423/10000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree093.table
  base := (-789028321279094901304756892939803331159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-366360590649082015470006111190000000000000)
      constant := (3987019627922721974724337761096246367732090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree093.table
  base := (-7890341976297095466833134652725626281119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-376545196030524622954338563560000000000000)
      constant := (4233767599086647289108359521909444312225169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269256053081135554229/100000000000000000000)
  centralHi := (26925605308113555423/10000000000000000000)
  directionLo := (135357723085956305381/50000000000000000000)
  directionHi := (270715446171912610763/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree094.table
  base := (-3938887158893630939072378194002214558767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-370412530424494665759471710520000000000000)
      constant := (4084991869062625277211328002064782973240834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree094.table
  base := (-1969456828084065390253865426584581490751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-190353323845879618382570535490000000000000)
      constant := (2168575355348661908584820294770711013906402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135357723085956305381/50000000000000000000)
  centralHi := (270715446171912610763/100000000000000000000)
  directionLo := (850521918529592741/312500000000000000)
  directionHi := (272167013929469677121/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree095.table
  base := (-3931753094701446673411571610457015136723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-374464470199907316048937309850000000000000)
      constant := (4184121182435969597127912524943962516601146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree095.table
  base := (-245736061783265541250232031532598394673/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-192434049676496925287971789200000000000000)
      constant := (2220874767040856949130519366490942858576368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (850521918529592741/312500000000000000)
  centralHi := (272167013929469677121/100000000000000000000)
  directionLo := (136805440449667944017/50000000000000000000)
  directionHi := (54722176179867177607/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree096.table
  base := (-313899167397257534252270319417457037887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-378516409975319966338402909180000000000000)
      constant := (4284407550535368782550113930425615128588425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree096.table
  base := (-49047014209448604729773147691727984577/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-194514775507114232193373042910000000000000)
      constant := (2273782027195674402873887338904426300458160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136805440449667944017/50000000000000000000)
  centralHi := (54722176179867177607/20000000000000000000)
  directionLo := (11001886734318763769/4000000000000000000)
  directionHi := (137523584178984547113/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree097.table
  base := (-1565938726102210158240314974063389442863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-382568349750732616627868508510000000000000)
      constant := (4385850957380053293132239483261219586498565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree097.table
  base := (-7829732478732529530768112384392784534579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-393191002675463078197548593240000000000000)
      constant := (4654594258050561486315141498177753557805629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11001886734318763769/4000000000000000000)
  centralHi := (137523584178984547113/50000000000000000000)
  directionLo := (138237997215819267633/50000000000000000000)
  directionHi := (276475994431638535267/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree098.table
  base := (-976268728038937454079890014525257317597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-55231469932306466702476301120000000000000)
      constant := (641207341194243492685549199665585590214568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree098.table
  base := (-7810184846505287294629613370588954866343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-56764636333813956001193014380000000000000)
      constant := (680405733232029126997900007309877315935599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138237997215819267633/50000000000000000000)
  centralHi := (276475994431638535267/100000000000000000000)
  directionLo := (69474368552451526309/25000000000000000000)
  directionHi := (277897474209806105237/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree099.table
  base := (-155776960787664062644248572022423385033/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-390672229301557917206799707170000000000000)
      constant := (4592208830094851755221869964595812706669150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree099.table
  base := (-973609951217413723165346671090859227121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-200756952998966152909576804040000000000000)
      constant := (2436150833349861143323248282294691591484284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69474368552451526309/25000000000000000000)
  centralHi := (277897474209806105237/100000000000000000000)
  directionLo := (139655859926657102329/50000000000000000000)
  directionHi := (279311719853314204659/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree100.table
  base := (-7765788526204522392221941558824642185981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-394724169076970567496265306500000000000000)
      constant := (4697123270312055518388594563617592532886931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree100.table
  base := (-7765816982620424931780297557465067452729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-405675357659166919629956115500000000000000)
      constant := (4982978849782011110781028484684211694816279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139655859926657102329/50000000000000000000)
  centralHi := (279311719853314204659/100000000000000000000)
  directionLo := (28071884069766799937/10000000000000000000)
  directionHi := (280718840697667999371/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree101.table
  base := (-483810719684979693494026418376103556931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-398776108852383217785730905830000000000000)
      constant := (4803194697732289071820416773193884811366096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree101.table
  base := (-7740997162524746697468420402935768689399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-409836809320401533440758622920000000000000)
      constant := (5094871672199640777179050322613147334219449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/10000000000000000000)
  centralHi := (280718840697667999371/100000000000000000000)
  directionLo := (282118943351681243493/100000000000000000000)
  directionHi := (141059471675840621747/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree102.table
  base := (-7714397217576135683601568927492643796353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-402828048627795868075196505160000000000000)
      constant := (4910423101971106167940593444205860453978703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree102.table
  base := (-385721016586288079061765685757170884531/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-206999130490818073625780565170000000000000)
      constant := (2603990062510605223698500829842986266579810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282118943351681243493/100000000000000000000)
  centralHi := (141059471675840621747/50000000000000000000)
  directionLo := (283512131791737542803/100000000000000000000)
  directionHi := (70878032947934385701/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree103.table
  base := (-7686065829547273387234406121371216703673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-406879988403208518364662104490000000000000)
      constant := (5018808473449331714384994309409560381520023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree103.table
  base := (-7686086658917455087198315707096039186813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-418159712642870761062363637760000000000000)
      constant := (5322304199980714831733132923465294079846163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283512131791737542803/100000000000000000000)
  centralHi := (70878032947934385701/25000000000000000000)
  directionLo := (28489850745190292163/10000000000000000000)
  directionHi := (284898507451902921631/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree104.table
  base := (-7655977531563202729240583828804819216583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-410931928178621168654127703820000000000000)
      constant := (5128350803313150099554174540700563858387433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree104.table
  base := (-7655996300573643499460612922760005849471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-422321164304105374873166145180000000000000)
      constant := (5437843889410936932266387973296759713375921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28489850745190292163/10000000000000000000)
  centralHi := (284898507451902921631/100000000000000000000)
  directionLo := (28627816931011070653/10000000000000000000)
  directionHi := (286278169310110706531/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree105.table
  base := (-7624132490970345444142515966966484154107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-59283409707719116991941900450000000000000)
      constant := (748435726194655236922362265162484610921251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree105.table
  base := (-3812074701080724436106218663105389664143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-30463043997524284905997760900000000000000)
      constant := (396757084727427697738674674495762272350999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28627816931011070653/10000000000000000000)
  centralHi := (286278169310110706531/100000000000000000000)
  directionLo := (287651213970625958553/100000000000000000000)
  directionHi := (143825606985312979277/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree106.table
  base := (-759053086307799543225139378894107598931/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-419035807729446469233058902480000000000000)
      constant := (5350906305987485989976829884318887276523810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree106.table
  base := (-7590546099224875133501330531211443325759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-430644067626574602494771160020000000000000)
      constant := (5672570083658211147483975793322639277037809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287651213970625958553/100000000000000000000)
  centralHi := (143825606985312979277/50000000000000000000)
  directionLo := (72254433935745971661/25000000000000000000)
  directionHi := (57803547148596777329/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree107.table
  base := (-7555172792328210056731585268681038884843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-423087747504859119522524501810000000000000)
      constant := (5463919464110187283320002594521379094642693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree107.table
  base := (-59024894674630335684382067191330800459/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-217402759643904608152786833720000000000000)
      constant := (2895878287815378898082286016684486609760576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72254433935745971661/25000000000000000000)
  centralHi := (57803547148596777329/20000000000000000000)
  directionLo := (58075565343516955799/20000000000000000000)
  directionHi := (72594456679396194749/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree108.table
  base := (-7518058413343595808450021092263646867559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-427139687280271769811990101140000000000000)
      constant := (5578089551134182820433574383127081303489609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree108.table
  base := (-7518070778043196158110106322685829734499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-438966970949043830116376174860000000000000)
      constant := (5912158656295209848986885770436394343009549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58075565343516955799/20000000000000000000)
  centralHi := (72594456679396194749/25000000000000000000)
  directionLo := (291731576838116925399/100000000000000000000)
  directionHi := (1458657884190584627/500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree109.table
  base := (-7479187851865990903770731194926995537143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-431191627055684420101455700470000000000000)
      constant := (5693416560898122528715707783309327218679993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree109.table
  base := (-3739599494738640283727315378421912678747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-221564211305139221963589341140000000000000)
      constant := (3016888160101852439346028973315826278741397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291731576838116925399/100000000000000000000)
  centralHi := (1458657884190584627/500000000000000000)
  directionLo := (29307907397096870651/10000000000000000000)
  directionHi := (293079073970968706511/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree110.table
  base := (-1859640306399412776071922046528406699689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-435243566831097070390921299800000000000000)
      constant := (5809900487634595875848298137205432286860956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree110.table
  base := (-464910703575593722925946713719308358003/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-223644937135756528868990594850000000000000)
      constant := (3078304781116534640046117877822031123662824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29307907397096870651/10000000000000000000)
  centralHi := (293079073970968706511/100000000000000000000)
  directionLo := (7360510099294535893/2500000000000000000)
  directionHi := (294420403971781435721/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree111.table
  base := (-7396178644955299569234612457971645933389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-439295506606509720680386899130000000000000)
      constant := (5927541325933183427028893145600139349263939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree111.table
  base := (-1849046919946587337233691077350198804403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-225725662966373835774391848560000000000000)
      constant := (3140329188777262369871503452768180517168506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7360510099294535893/2500000000000000000)
  centralHi := (294420403971781435721/100000000000000000000)
  directionLo := (59151130149857120323/20000000000000000000)
  directionHi := (18484728171830350101/6250000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree112.table
  base := (-735204021374629049595682909097599209453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-63335349483131767281407499780000000000000)
      constant := (863762724386760689512510268507168055338290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree112.table
  base := (-91900604378743736403512881533196030199/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-32543769828141591811399014610000000000000)
      constant := (457565911543327105479961535042705111544280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59151130149857120323/20000000000000000000)
  centralHi := (18484728171830350101/6250000000000000000)
  directionLo := (37135612040819352983/12500000000000000000)
  directionHi := (59416979265310964773/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree113.table
  base := (-7306146029775145085151479028225787616043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-447399386157335021259318097790000000000000)
      constant := (6166293717164598535690174432843686406813893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree113.table
  base := (-7306153356881089061713925818849043923451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-459774229255216899170388711960000000000000)
      constant := (6532402710070758591583460502609396847750901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37135612040819352983/12500000000000000000)
  centralHi := (59416979265310964773/20000000000000000000)
  directionLo := (14920411044990202859/5000000000000000000)
  directionHi := (298408220899804057181/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree114.table
  base := (-7258496185387833991545581059374016467417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-451451325932747671548783697120000000000000)
      constant := (6287405260780051992255076884787673193096567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree114.table
  base := (-3629251391573685252422269215400427649643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-231967840458225756490595609690000000000000)
      constant := (3330049109424932899831030309081379045167493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14920411044990202859/5000000000000000000)
  centralHi := (298408220899804057181/100000000000000000000)
  directionLo := (299725702894851314999/100000000000000000000)
  directionHi := (59945140578970263/20000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree115.table
  base := (-1802272691990097827536923017880807444513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-455503265708160321838249296450000000000000)
      constant := (6409673697272259525626859947914111740875452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree115.table
  base := (-1441819341719254470875776965290727739681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-468097132577686126791993726800000000000000)
      constant := (6789009284048502574432667030328771703778155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299725702894851314999/100000000000000000000)
  centralHi := (59945140578970263/20000000000000000)
  directionLo := (301037419021355398317/100000000000000000000)
  directionHi := (150518709510677699159/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree116.table
  base := (-1431585972067548197555013106925953988173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-459555205483572972127714895780000000000000)
      constant := (6533099022581819862411478202195141272897615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree116.table
  base := (-715793520896387958709306284770000632537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-236129292119460370301398117110000000000000)
      constant := (3459567950977800376016625472427349845028435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301037419021355398317/100000000000000000000)
  centralHi := (150518709510677699159/50000000000000000000)
  directionLo := (15117172216246788529/5000000000000000000)
  directionHi := (302343444324935770581/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree117.table
  base := (-71050135412279881468687128388176329911/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-463607145258985622417180495110000000000000)
      constant := (6657681232852035851609322089514685983436100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree117.table
  base := (-3552509178272126415036072793752192994127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-238210017950077677206799370820000000000000)
      constant := (3525239034514375680868321890092642543287777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15117172216246788529/5000000000000000000)
  centralHi := (302343444324935770581/100000000000000000000)
  directionLo := (60728770447454956867/20000000000000000000)
  directionHi := (18977740764829674021/6250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree118.table
  base := (-7050341885556866971456017113893541174909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-467659085034398272706646094440000000000000)
      constant := (6783420324411546518203049836512216482429459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree118.table
  base := (-7050346220476538754505995459490664129647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-480581487561389968224401249060000000000000)
      constant := (7183035781880136216654542278052957457647297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60728770447454956867/20000000000000000000)
  centralHi := (18977740764829674021/6250000000000000000)
  directionLo := (60987742924859381973/20000000000000000000)
  directionHi := (152469357312148454933/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree119.table
  base := (-3496957482393268115946033843139094264963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-67387289258544417570873099110000000000000)
      constant := (987188041965529440349323152313302680290518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree119.table
  base := (-6993918867002887700955422254112350841169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-69248991317517797433600536640000000000000)
      constant := (1045258433894841421442780965532213544111817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60987742924859381973/20000000000000000000)
  centralHi := (152469357312148454933/50000000000000000000)
  directionLo := (306228101832514412889/100000000000000000000)
  directionHi := (30622810183251441289/10000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree120.table
  base := (-6935732847202466707376682245237773483631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-475762964585223573285577293100000000000000)
      constant := (7038369137547526476155167711783349099302081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree120.table
  base := (-3467868179850155511381961058982037617397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-244452195441929597923003131950000000000000)
      constant := (3725898916032369502878792955509880156747547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306228101832514412889/100000000000000000000)
  centralHi := (30622810183251441289/10000000000000000000)
  directionLo := (307512082733624052563/100000000000000000000)
  directionHi := (76878020683406013141/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree121.table
  base := (-1375159119634353180256809257579268137339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-479814904360636223575042892430000000000000)
      constant := (7167578852575019431667431683923829306351945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree121.table
  base := (-3437899379844634379585401202175904215293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-246532921272546904828404385660000000000000)
      constant := (3794001081643890420853086837311880693450643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307512082733624052563/100000000000000000000)
  centralHi := (76878020683406013141/25000000000000000000)
  directionLo := (308790724767434799307/100000000000000000000)
  directionHi := (77197681191858699827/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree122.table
  base := (-170352582009398234040105915135958486929/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-483866844136048873864508491760000000000000)
      constant := (7297945435769791667130540219846521365619160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree122.table
  base := (-6654400513497533168049247124624731671/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-248613647103164211733805639370000000000000)
      constant := (3862711014024640759151909059181414731837952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308790724767434799307/100000000000000000000)
  centralHi := (77197681191858699827/25000000000000000000)
  directionLo := (310064093983202283049/100000000000000000000)
  directionHi := (6201281879664045661/2000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree123.table
  base := (-1350131190804138001110607138156624269941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-487918783911461524153974091090000000000000)
      constant := (7429468884181762269600919977398377053864455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree123.table
  base := (-6750658514849129166831197858133387988633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-501388745867563037278413786160000000000000)
      constant := (7864057423568383111613231848704463988556983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310064093983202283049/100000000000000000000)
  centralHi := (6201281879664045661/2000000000000000000)
  directionLo := (311332255079441656717/100000000000000000000)
  directionHi := (155666127539720828359/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree124.table
  base := (-417840854814084561965263217848563384679/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-491970723686874174443439690420000000000000)
      constant := (7562149194972885286321196327438726306411664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree124.table
  base := (-417840998848598083441058698066028114289/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-252775098764398825544608146790000000000000)
      constant := (4001954173579812104110031589074116979198712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311332255079441656717/100000000000000000000)
  centralHi := (155666127539720828359/50000000000000000000)
  directionLo := (156297635721143389513/50000000000000000000)
  directionHi := (312595271442286779027/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree125.table
  base := (-3231687746676635847311356460661949419/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-496022663462286824732905289750000000000000)
      constant := (7695986365408772954386590461928402051904512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree125.table
  base := (-827312322375383883035301359235315042473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-254855824595016132450009400500000000000000)
      constant := (4072487398113093627471848485152378251675292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156297635721143389513/50000000000000000000)
  centralHi := (312595271442286779027/100000000000000000000)
  directionLo := (313853205182460068069/100000000000000000000)
  directionHi := (31385320518246006807/10000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree126.table
  base := (-818723061546090270506440433308924489339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-71439229033957067860338698440000000000000)
      constant := (1118711484693018012848077874585700228597016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree126.table
  base := (-6549786358437396614929764207043406075323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-73410442978752411244403044060000000000000)
      constant := (1183893824036256557289063973526696157472739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313853205182460068069/100000000000000000000)
  centralHi := (31385320518246006807/10000000000000000000)
  directionLo := (78776529292728509351/25000000000000000000)
  directionHi := (63021223434182807481/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree127.table
  base := (-3239658845285916357592449883092230120001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-504126543013112125311836488410000000000000)
      constant := (7967131274750888062975172801153711448239902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree127.table
  base := (-6479319369620471260024704529391379025727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-518034552512501492521623815840000000000000)
      constant := (8430754260805193808081056148612822427739377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78776529292728509351/25000000000000000000)
  centralHi := (63021223434182807481/20000000000000000000)
  directionLo := (316354067073202384961/100000000000000000000)
  directionHi := (158177033536601192481/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree128.table
  base := (-6407096150129841931986974881722041965381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-508178482788524775601302087740000000000000)
      constant := (8104439008642047630401107289483619943696331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree128.table
  base := (-1601774415205610221897161694325017534071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-261098002086868053166213161630000000000000)
      constant := (4287733635757571913801736320100148281661042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316354067073202384961/100000000000000000000)
  centralHi := (158177033536601192481/50000000000000000000)
  directionLo := (158798556691317774421/50000000000000000000)
  directionHi := (317597113382635548843/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree129.table
  base := (-1583279979947325161233076407892233502443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-512230422563937425890767687070000000000000)
      constant := (8242903592136023801521095302983872233521172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree129.table
  base := (-6333121278936221868203949314548921713493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-526357455834970720143228830680000000000000)
      constant := (8721395798085893057432161729624102836038843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158798556691317774421/50000000000000000000)
  centralHi := (317597113382635548843/100000000000000000000)
  directionLo := (31883531345227286079/10000000000000000000)
  directionHi := (318835313452272860791/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree130.table
  base := (-6257389046820486561378851649622934856311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-516282362339350076180233286400000000000000)
      constant := (8382525022916572968674596819593476192040761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree130.table
  base := (-625739026956153502481232029055963407893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-265259453748102666977015669050000000000000)
      constant := (4434269919141527588621489858781288965066215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31883531345227286079/10000000000000000000)
  centralHi := (318835313452272860791/100000000000000000000)
  directionLo := (320068723525800806263/100000000000000000000)
  directionHi := (40008590440725100783/12500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree131.table
  base := (-6179903577111772962162274530420415046179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-520334302114762726469698885730000000000000)
      constant := (8523303298735164841100664421180149662737229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree131.table
  base := (-6179904677081308504842140210121407054379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-534680359157439947764833845520000000000000)
      constant := (9016899389931866707811935959281051054335429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320068723525800806263/100000000000000000000)
  centralHi := (40008590440725100783/12500000000000000000)
  directionLo := (321297398767344429207/100000000000000000000)
  directionHi := (40162174845918053651/12500000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree132.table
  base := (-3050331777627703038135627065450446566193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-524386241890175376759164485060000000000000)
      constant := (8665238417406779353578852794753856236513086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree132.table
  base := (-6100664544731239009855200189427396884249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-538841810818674561575636352940000000000000)
      constant := (9166474450913778510762502690086057552671799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321297398767344429207/100000000000000000000)
  centralHi := (40162174845918053651/12500000000000000000)
  directionLo := (322521393290256590029/100000000000000000000)
  directionHi := (32252139329025659003/10000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree133.table
  base := (-3009834512312782251767837568761731201609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-75491168809369718149804297770000000000000)
      constant := (1258332910972297393531071084382585763177474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree133.table
  base := (-6019669914663215900195586391052200469967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-77571894639987025055205551480000000000000)
      constant := (1331037859880478286776831384001634596710231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322521393290256590029/100000000000000000000)
  centralHi := (32252139329025659003/10000000000000000000)
  directionLo := (323740760184927587697/100000000000000000000)
  directionHi := (161870380092463793849/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree134.table
  base := (-5936920027449482268266816810269645718719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-532490121441000677338095683720000000000000)
      constant := (8952579174863937577325346125213787359782769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree134.table
  base := (-5936920828003237018712507955747866007069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-547164714141143789197241367780000000000000)
      constant := (9469271092665401303538275705160354565653619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323740760184927587697/100000000000000000000)
  centralHi := (161870380092463793849/50000000000000000000)
  directionLo := (40619443943206947891/12500000000000000000)
  directionHi := (324955551545655583129/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree135.table
  base := (-731552075609041882887155946247000127303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-536542061216413327627561283050000000000000)
      constant := (9097984809564233212463402545739925950097224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree135.table
  base := (-2926208662452188825695469900937572559711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-275663082901189201504021937600000000000000)
      constant := (4811246334726218855025303485266558944574161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40619443943206947891/12500000000000000000)
  centralHi := (324955551545655583129/100000000000000000000)
  directionLo := (81541454624154075761/25000000000000000000)
  directionHi := (65233163699323260609/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree136.table
  base := (-1153231759403303187436469522081439688443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-540594000991825977917026882380000000000000)
      constant := (9244547278940971400723053222762047276331465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree136.table
  base := (-5766159444595313959001006184830136677333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-555487617463613016818846382620000000000000)
      constant := (9776929747602252095097077395615323302810683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81541454624154075761/25000000000000000000)
  centralHi := (65233163699323260609/20000000000000000000)
  directionLo := (327371611216968654107/100000000000000000000)
  directionHi := (81842902804242163527/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree137.table
  base := (-177442082594870661369302417549113834869/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-544645940767238628206492481710000000000000)
      constant := (9392266581075614164712815695209739506925408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree137.table
  base := (-2839073612712424333734214409194131195181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-279824534562423815314824445020000000000000)
      constant := (4966291162617876562553663308215987571436131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327371611216968654107/100000000000000000000)
  centralHi := (81842902804242163527/25000000000000000000)
  directionLo := (16428648948256556479/5000000000000000000)
  directionHi := (328572978965131129581/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree138.table
  base := (-698547522645666057135215824776388610509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-548697880542651278495958081040000000000000)
      constant := (9541142714094648576442843964120655664680472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree138.table
  base := (-1117676140980567815833933485784992567729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-563810520786082244440451397460000000000000)
      constant := (10089450400514957792264908106390676820906395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16428648948256556479/5000000000000000000)
  centralHi := (328572978965131129581/100000000000000000000)
  directionLo := (10305311565695694959/3125000000000000000)
  directionHi := (329769970102262238689/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree139.table
  base := (-2748429724383288676189338950533367948279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-552749820318063928785423680370000000000000)
      constant := (9691175676167353318678333083038479941068658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree139.table
  base := (-5496859919737884925212459610835988586717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-567971972447316858251253904880000000000000)
      constant := (10247533971641144709745542723366036559250867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10305311565695694959/3125000000000000000)
  centralHi := (329769970102262238689/100000000000000000000)
  directionLo := (165481316057488313213/50000000000000000000)
  directionHi := (330962632114976626427/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree140.table
  base := (-5403584482369854758490391796416015828711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-79543108584782368439269897100000000000000)
      constant := (1406052209357678041841281698025087889199023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree140.table
  base := (-5403584905872095652544496184242530644269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-81733346301221638866008058900000000000000)
      constant := (1486690433836164359235541945310302285490117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165481316057488313213/50000000000000000000)
  centralHi := (330962632114976626427/100000000000000000000)
  directionLo := (16607550581866353663/5000000000000000000)
  directionHi := (332151011637327073261/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree141.table
  base := (-5308555317712546836922133080419311558707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-560853699868889229364354879030000000000000)
      constant := (9994712080352695577161002398520203733623357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree141.table
  base := (-5308555698513222924476196319796663253021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-576294875769786085872858919720000000000000)
      constant := (10567347594425795375472450248446963500601971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16607550581866353663/5000000000000000000)
  centralHi := (332151011637327073261/100000000000000000000)
  directionLo := (333335154472081164983/100000000000000000000)
  directionHi := (41666894309010145623/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree142.table
  base := (-5211771989774720939279793087937302288337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-564905639644301879653820478360000000000000)
      constant := (10148215519000177871265735944664072187871487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree142.table
  base := (-5211772332164413959339852719992767169301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-580456327431020699683661427140000000000000)
      constant := (10729077642668425078518230274768354408704251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333335154472081164983/100000000000000000000)
  centralHi := (41666894309010145623/12500000000000000000)
  directionLo := (334515105611320098003/100000000000000000000)
  directionHi := (83628776402830024501/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree143.table
  base := (-5113234532811947863345133613737807850549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-568957579419714529943286077690000000000000)
      constant := (10302875779767670206111866196663597415323099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree143.table
  base := (-5113234840651814439567574978231081744157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-584617779092255313494463934560000000000000)
      constant := (10892023179923558485346960326059676994536307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334515105611320098003/100000000000000000000)
  centralHi := (83628776402830024501/25000000000000000000)
  directionLo := (67138181851277166069/20000000000000000000)
  directionHi := (167845454628192915173/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree144.table
  base := (-626617872548208093980246570436432617629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-573009519195127180232751677020000000000000)
      constant := (10458692861010662161705926077140918413889432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree144.table
  base := (-1253235814287556434024151185985979834263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-294389615376744963652633220990000000000000)
      constant := (5528092102282815164391357780749373976242226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67138181851277166069/20000000000000000000)
  centralHi := (167845454628192915173/50000000000000000000)
  directionLo := (84215652209300399811/25000000000000000000)
  directionHi := (67372521767440319849/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree145.table
  base := (-4910897365391312178555676761340960088093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-577061458970539830522217276350000000000000)
      constant := (10615666761117277149932432611713042955683443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree145.table
  base := (-1227724403551749948461983088872510521063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-296470341207362270558034474700000000000000)
      constant := (5610780357499910181762183727252993968935826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84215652209300399811/25000000000000000000)
  centralHi := (67372521767440319849/20000000000000000000)
  directionLo := (338030247030989698713/100000000000000000000)
  directionHi := (169015123515494849357/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree146.table
  base := (-600887215010556876039416500120714885843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-581113398745952480811682875680000000000000)
      constant := (10773797478506992492414760596489679764749544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree146.table
  base := (-4807097943764335930628510717684406133911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-597102134075959154926871456820000000000000)
      constant := (11388152709660960822999375312745464099438361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338030247030989698713/100000000000000000000)
  centralHi := (169015123515494849357/50000000000000000000)
  directionLo := (847984664451023353/250000000000000000)
  directionHi := (339193865780409341201/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree147.table
  base := (-2350772038052537590184270482769640753059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-83595048360195018728735496430000000000000)
      constant := (1561869287375635582018539642856475029457174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree147.table
  base := (-4701544277180126762912315757613112082983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-85894797962456252676810566320000000000000)
      constant := (1650851455287502138428644902255708215419119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (847984664451023353/250000000000000000)
  centralHi := (339193865780409341201/100000000000000000000)
  directionLo := (68070701262227282593/20000000000000000000)
  directionHi := (170176753155568206483/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree148.table
  base := (-45942364645002053809338909639576560653/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-589217278296777781390614074340000000000000)
      constant := (11093529358963342293452772544094074852800300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree148.table
  base := (-4594236645247485263827446725505770662687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-605425037398428382548476471660000000000000)
      constant := (11724983145545620265844507600378217237528337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68070701262227282593/20000000000000000000)
  centralHi := (170176753155568206483/50000000000000000000)
  directionLo := (341509209148905970063/100000000000000000000)
  directionHi := (21344325571806623129/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree149.table
  base := (-1121293728936263850190444763114473898269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-593269218072190431680079673670000000000000)
      constant := (11255130519015386870636976273030313115939276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree149.table
  base := (-4485175078213071381956872169890573684251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-609586489059662996359278979080000000000000)
      constant := (11895221583778190376050789707632361889471701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341509209148905970063/100000000000000000000)
  centralHi := (21344325571806623129/6250000000000000000)
  directionLo := (342661014136037407719/100000000000000000000)
  directionHi := (8566525353400935193/2500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree150.table
  base := (-1093589864940691900924450829224246382659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-597321157847603081969545273000000000000000)
      constant := (11417888490319348829853954380597047708998836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree150.table
  base := (-2187179802897162263458902397832989247517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-306873970360448805085040743250000000000000)
      constant := (6033337750127035384274058607506183526871667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342661014136037407719/100000000000000000000)
  centralHi := (8566525353400935193/2500000000000000000)
  directionLo := (171904480223730683891/50000000000000000000)
  directionHi := (343808960447461367783/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree151.table
  base := (-4261790125942924171455983343099658801789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-601373097623015732259010872330000000000000)
      constant := (11581803271435138644199719907088866718712339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree151.table
  base := (-1065447564298924350247533235765498726577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-308954696191066111990441996960000000000000)
      constant := (6119672446771121630462387796923481124795454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171904480223730683891/50000000000000000000)
  centralHi := (343808960447461367783/100000000000000000000)
  directionLo := (172476543303133312063/50000000000000000000)
  directionHi := (344953086606266624127/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree152.table
  base := (-4147466943158916467591413426386632860339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-605425037398428382548476471660000000000000)
      constant := (11746874860947960136860073232035054989843389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree152.table
  base := (-4147467061123976984687410309904188321787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-622070844043366837791686501340000000000000)
      constant := (12413229762236075291135600712942694772232437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172476543303133312063/50000000000000000000)
  centralHi := (344953086606266624127/100000000000000000000)
  directionLo := (21630839406174025123/6250000000000000000)
  directionHi := (346093430498784401969/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree153.table
  base := (-503923742473034478444991842794033438427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-609476977173841032837942070990000000000000)
      constant := (11913103257467510272397678137831488892136616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree153.table
  base := (-2015695022901384921347692465157636750771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-313116147852300725801244504380000000000000)
      constant := (6294165052476305068755495459313775799212221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21630839406174025123/6250000000000000000)
  centralHi := (346093430498784401969/100000000000000000000)
  directionLo := (173615014694613420911/50000000000000000000)
  directionHi := (347230029389226841823/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree154.table
  base := (-1956779571854027597806777117432356775377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-87646988135607669018201095760000000000000)
      constant := (1725784065661032208077740897746947005144722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree154.table
  base := (-15654236955944884773553063377028623801/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-45028124811845433243806536870000000000000)
      constant := (911760422880849620310757854853099954174125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173615014694613420911/50000000000000000000)
  centralHi := (347230029389226841823/100000000000000000000)
  directionLo := (34836291993389560997/10000000000000000000)
  directionHi := (348362919933895609971/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree155.table
  base := (-3793974582349342171543282048338762763399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-617580856724666333416873269650000000000000)
      constant := (12249030466083570396909838174150150624593449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree155.table
  base := (-3793974667972030280797250942224148461409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-634555199027070679224094023600000000000000)
      constant := (12942177207036341668696929164256016725390959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34836291993389560997/10000000000000000000)
  centralHi := (348362919933895609971/100000000000000000000)
  directionLo := (174746069097487991511/50000000000000000000)
  directionHi := (349492138194975983023/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree156.table
  base := (-3672636282670976092155643968974132489097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-621632796500078983706338868980000000000000)
      constant := (12418729275515365965991114044072267508034247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree156.table
  base := (-3672636359613818413749007113064864134873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-638716650688305293034896531020000000000000)
      constant := (13120923963750123646417441830011821657391223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174746069097487991511/50000000000000000000)
  centralHi := (349492138194975983023/100000000000000000000)
  directionLo := (350617719653931092363/100000000000000000000)
  directionHi := (87654429913482773091/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree157.table
  base := (-3549544271192534656829006853822736204377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-625684736275491633995804468310000000000000)
      constant := (12589584886623152856518473917999435925985527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree157.table
  base := (-3549544340332900514075386896786021585481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-642878102349539906845699038440000000000000)
      constant := (13300886189178596186342387190750484942311431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350617719653931092363/100000000000000000000)
  centralHi := (87654429913482773091/25000000000000000000)
  directionLo := (351739699224510403341/100000000000000000000)
  directionHi := (175869849612255201671/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree158.table
  base := (-1712349287001324613350239042397203255479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-629736676050904284285270067640000000000000)
      constant := (12761597298128588131796199534218074080963058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree158.table
  base := (-3424698636129506073942240213630925902921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-647039554010774520656501545860000000000000)
      constant := (13482063882047748043355638600380084630756871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351739699224510403341/100000000000000000000)
  centralHi := (175869849612255201671/50000000000000000000)
  directionLo := (352858111265385922221/100000000000000000000)
  directionHi := (176429055632692961111/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree159.table
  base := (-164904960838535110273443089541376284269/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-633788615826316934574735666970000000000000)
      constant := (12934766508773872054043049490410201241416380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree159.table
  base := (-3298099272593490998839397606663196961009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-651201005672009134467304053280000000000000)
      constant := (13664457041103676278088194362290503348910559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352858111265385922221/100000000000000000000)
  centralHi := (176429055632692961111/50000000000000000000)
  directionLo := (88493247398107267429/25000000000000000000)
  directionHi := (353972989592429069717/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree160.table
  base := (-792436556189488694273791467769022906901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-637840555601729584864201266300000000000000)
      constant := (13109092517321202825244934399517271510247404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree160.table
  base := (-3169746274914577851728743278952510170111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-655362457333243748278106560700000000000000)
      constant := (13848065665112084484954922150531327001664561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88493247398107267429/25000000000000000000)
  centralHi := (353972989592429069717/100000000000000000000)
  directionLo := (44385545936330078969/12500000000000000000)
  directionHi := (355084367490640631753/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree161.table
  base := (-303963962282814866995713678598898556363/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-91698927911020319307666695090000000000000)
      constant := (1897796474650322442958763526425327101054590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree161.table
  base := (-3039639667892158465577596695684678322467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (102)
      previous := (38)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-94217701284925480298415581160000000000000)
      constant := (2004698536122543209162917615901207251742731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44385545936330078969/12500000000000000000)
  centralHi := (355084367490640631753/100000000000000000000)
  directionLo := (178096138862872847359/50000000000000000000)
  directionHi := (356192277725745694719/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree162.table
  base := (-2907779435457621482832027989764063262697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-645944435152554885443132464960000000000000)
      constant := (13461214923267694338102194927534560900127847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree162.table
  base := (-1453889737972344855803666514992153699573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-331842680327856487949855787770000000000000)
      constant := (7109464651572162914477425230569384468720923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178096138862872847359/50000000000000000000)
  centralHi := (356192277725745694719/100000000000000000000)
  directionLo := (357296752555464992447/100000000000000000000)
  directionHi := (5582761758679140507/1562500000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree163.table
  base := (-1387082843372485697989346803013297147033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-649996374927967535732598064290000000000000)
      constant := (13639011318286683226584801275131446879590766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree163.table
  base := (-554833144623742071915489834843496353393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-667846812316947589710514082960000000000000)
      constant := (14406184314793374179679988252296343393418715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357296752555464992447/100000000000000000000)
  centralHi := (5582761758679140507/1562500000000000000)
  directionLo := (179198911870236817187/50000000000000000000)
  directionHi := (114687303596951563/32000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree164.table
  base := (-1319399200210151878144280889628841892921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-654048314703380186022063663620000000000000)
      constant := (13817964506446448604161483748688373494493742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree164.table
  base := (-2638798433097504409049267908299227122139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-672008263978182203521316590380000000000000)
      constant := (14594654786644466600337331868565337871015189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179198911870236817187/50000000000000000000)
  centralHi := (114687303596951563/32000000000000000)
  directionLo := (359495522555057747523/100000000000000000000)
  directionHi := (89873880638764436881/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree165.table
  base := (-2501677599854089029448947240492863209503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-658100254478792836311529262950000000000000)
      constant := (13998074486601837418013563926384599702734353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree165.table
  base := (-1250838814604716987731972078757106063391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-338084857819708408666059548900000000000000)
      constant := (7392170358777256673635132359303401802893841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359495522555057747523/100000000000000000000)
  centralHi := (89873880638764436881/25000000000000000000)
  directionLo := (180294939898739574079/50000000000000000000)
  directionHi := (360589879797479148159/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree166.table
  base := (-2362803308065658918888630311958511050827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-662152194254205486600994862280000000000000)
      constant := (14179341257624902414673031572431032958509477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree166.table
  base := (-2362803334435962753979440226711338868177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-680331167300651431142921605220000000000000)
      constant := (14975242106397422699416046649483144395459327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180294939898739574079/50000000000000000000)
  centralHi := (360589879797479148159/100000000000000000000)
  directionLo := (361680925800057761007/100000000000000000000)
  directionHi := (22605057862503610063/6250000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree167.table
  base := (-2222175547731365029375343970609496826823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-666204134029618136890460461610000000000000)
      constant := (14361764818404502365506267770956884655485673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree167.table
  base := (-2222175571419389232428507995866872840997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (714)
      previous := (266)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-684492618961886044953724112640000000000000)
      constant := (15167358952063722030870872819075523230791147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361680925800057761007/100000000000000000000)
  centralHi := (22605057862503610063/6250000000000000000)
  directionLo := (18138434521949056201/5000000000000000000)
  directionHi := (362768690438981124021/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree168.table
  base := (-259974292649052784272218736186385106819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (103)
      previous := (37)
      next := (0)
      square := (1095118858219635213369080900000000000000)
      linear := (-95750867686432969597132294420000000000000)
      constant := (2077906452549416819966158299997562434018136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree168.table
  base := (-519948590617576790045025250742335779649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (51)
      previous := (19)
      next := (0)
      square := (547559429109817606684540450000000000000)
      linear := (-49189576473080047054609044290000000000000)
      constant := (1097192232390013731993976036001607299084914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell002.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18138434521949056201/5000000000000000000)
  centralHi := (362768690438981124021/100000000000000000000)
  directionLo := (181926601571924976841/50000000000000000000)
  directionHi := (363853203143849953683/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree169.table
  base := (-967829855231228631721719373917649686389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (721)
      previous := (259)
      next := (0)
      square := (7665832007537446493583566300000000000000)
      linear := (-674308013580443437469391660270000000000000)
      constant := (14730082304870480833546320616226820330733878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree169.table
  base := (-483914932393702320577002192886048295349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (357)
      previous := (133)
      next := (0)
      square := (3832916003768723246791783150000000000000)
      linear := (-346407761142177636287664563740000000000000)
      constant := (7777619504754757403020903008835667267055798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell002.Kernel169
