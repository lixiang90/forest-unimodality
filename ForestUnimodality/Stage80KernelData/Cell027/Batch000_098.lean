import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell027.Parameters
import ForestUnimodality.BinomialMassData.Q301_666.Batch000_049
import ForestUnimodality.BinomialMassData.Q301_666.Batch050_099
import ForestUnimodality.BinomialMassData.Q17_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q17_37.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree000.table
  base := (15979242276676060142133195433981/500000000000000000000000000000)
  polynomial :=
    { denominator := 6660000000000000000000000000000000000000000
      center := (25915)
      previous := (21371)
      next := (0)
      square := (903313577059516222833579460200000000000000)
      linear := (3513245897615337773878252415400000000000000)
      constant := (212843507125325121093214163180626920000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree000.table
  base := (15979242276676060142133195433981/500000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1420)
      previous := (1207)
      next := (0)
      square := (50184087614417567935198858900000000000000)
      linear := (195180327645296542993236245300000000000000)
      constant := (11824639284740284505178564621145940000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree001.table
  base := (199318898881160733815805247752165290786281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (898013497210993095628550636808000000000000000)
      constant := (43737245525798657511834289407126863859999827618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree001.table
  base := (39467567392142746796374672031273898998097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (5515413143985774780952979873500000000000000)
      constant := (267229411643316430242550221187269838641973965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49768603062450172227/100000000000000000000)
  directionHi := (12442150765612543057/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree002.table
  base := (63871328603579501670476349661957469823427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (626116110516078712555643219287800000000000000)
      constant := (27518793124201895263417694412283207484999986412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree002.table
  base := (12541094953200984742444390521240312377693/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (3809154165095577471156218670900000000000000)
      constant := (166619372425658877271296103108779876450617170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/100000000000000000000)
  centralHi := (12442150765612543057/25000000000000000000)
  directionLo := (70383433431280185901/100000000000000000000)
  directionHi := (35191716715640092951/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree003.table
  base := (16875146778740211711023802450463514060123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (39357635980129369942526200196400000000000000)
      constant := (1964381276068579329193660530080559567347754830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree003.table
  base := (41141661414628678915283128121048171338619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (2102895186205380161359457468300000000000000)
      constant := (106219477969967526047645622014829893125138822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/100000000000000000000)
  centralHi := (35191716715640092951/50000000000000000000)
  directionLo := (17240349825178344083/20000000000000000000)
  directionHi := (2693804660184116263/3125000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree004.table
  base := (57431882238310389072428255737929036484573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (82321337126249946409828384247400000000000000)
      constant := (11605230385862778089451248301613225853475630794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree004.table
  base := (55725295050468093971908517449850122818219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (396636207315182851562696265700000000000000)
      constant := (69287321269320570160012412561244818138141811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17240349825178344083/20000000000000000000)
  centralHi := (2693804660184116263/3125000000000000000)
  directionLo := (49768603062450172227/50000000000000000000)
  directionHi := (19907441224980068891/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree005.table
  base := (40129088044761967837790549649862369394027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-189576049568664436663079033272800000000000000)
      constant := (7792088283528193593318881569279926559468520006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree005.table
  base := (38786033380843154582286014723660539390989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-1309622771575014458234064936900000000000000)
      constant := (46307212200258313774989655888691278426263941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/50000000000000000000)
  centralHi := (19907441224980068891/20000000000000000000)
  directionLo := (11128597959284279629/10000000000000000000)
  directionHi := (111285979592842796291/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree006.table
  base := (28573372382643443973428807568605871776881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-51274826251508757748442938977000000000000000)
      constant := (597378479820496680152688655753185892325901602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree006.table
  base := (344028640810422250750822848735423078109/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-3015881750465211768030826139500000000000000)
      constant := (31880846228234504997941884291703535514497680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11128597959284279629/10000000000000000000)
  centralHi := (111285979592842796291/100000000000000000000)
  directionLo := (15238460339264895269/12500000000000000000)
  directionHi := (121907682714119162153/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree007.table
  base := (20509273020748126892852446854691432234233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-733370822958493202808893868313200000000000000)
      constant := (3857972587719050248726488862493506458043726274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree007.table
  base := (9838357516315524110748468702365497884633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-4722140729355409077827587342100000000000000)
      constant := (22917906179280729359313951978076733208125154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15238460339264895269/12500000000000000000)
  centralHi := (121907682714119162153/100000000000000000000)
  directionLo := (65837673401165370751/50000000000000000000)
  directionHi := (131675346802330741503/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree008.table
  base := (2924358633470405743190906108650986841123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-1005268209653407585881801285833400000000000000)
      constant := (2945149733056971391301398185230792798252883470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree008.table
  base := (6973887423997893244568831278744542186713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-6428399708245606387624348544700000000000000)
      constant := (17636597707585559600588198091602556507220194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65837673401165370751/50000000000000000000)
  centralHi := (131675346802330741503/100000000000000000000)
  directionLo := (70383433431280185901/50000000000000000000)
  directionHi := (140766866862560371803/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree009.table
  base := (5068392431574604483261143770104779576683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-141907288483146885439412078150400000000000000)
      constant := (274027640919920075796156658031793956657244972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree009.table
  base := (239425741235101917838205890413357755217/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-8134658687135803697421109747300000000000000)
      constant := (14998614999922751775154200595435470675682920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/50000000000000000000)
  centralHi := (140766866862560371803/100000000000000000000)
  directionLo := (149305809187350516681/100000000000000000000)
  directionHi := (74652904593675258341/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree010.table
  base := (6592200552530615564135117705126613555539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-1549062983043236352027616120873800000000000000)
      constant := (2318797710598113769027004215715570101120328342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree010.table
  base := (6115784691165204769050379534631669475977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-9840917666026001007217870949900000000000000)
      constant := (14389694949441718245040538211910755512612513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149305809187350516681/100000000000000000000)
  centralHi := (74652904593675258341/50000000000000000000)
  directionLo := (78691070821086884317/50000000000000000000)
  directionHi := (31476428328434753727/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree011.table
  base := (3707024381032214500623621238563867649849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-1820960369738150735100523538394000000000000000)
      constant := (2440473425842146117622387916798367439648211522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree011.table
  base := (1646510837124080876976892878273302702757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-11547176644916198317014632152500000000000000)
      constant := (15438813504769007823751038528912302800148666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78691070821086884317/50000000000000000000)
  centralHi := (31476428328434753727/20000000000000000000)
  directionLo := (165063782698279913367/100000000000000000000)
  directionHi := (20632972837284989171/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree012.table
  base := (653020780361449625880172356166591569197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-232539750714785013130381217323800000000000000)
      constant := (310268569863732531691271651015314298896304948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree012.table
  base := (940502451466522773509055697236541408283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-13253435623806395626811393355100000000000000)
      constant := (17915652642406404830401154883516825187939427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165063782698279913367/100000000000000000000)
  centralHi := (20632972837284989171/12500000000000000000)
  directionLo := (172403498251783440831/100000000000000000000)
  directionHi := (2693804660184116263/1562500000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree013.table
  base := (-361728976825119657580197005106520805967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-2364755143127979501246338373434400000000000000)
      constant := (3349632210976354090190974269832522057388501348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree013.table
  base := (-41993286581780335117232062681479830401/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-14959694602696592936608154557700000000000000)
      constant := (21672279334851503259460156701126352804525775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172403498251783440831/100000000000000000000)
  centralHi := (2693804660184116263/1562500000000000000)
  directionLo := (179443250249878222051/100000000000000000000)
  directionHi := (44860812562469555513/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree014.table
  base := (-491339291516945899120688600127848829139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-2636652529822893884319245790954600000000000000)
      constant := (4095436022199579202219373073267029711856054290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree014.table
  base := (-343775416915488600687739447627440424671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-16665953581586790246404915760300000000000000)
      constant := (26609822811957443453996682634984272469003208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179443250249878222051/100000000000000000000)
  centralHi := (44860812562469555513/25000000000000000000)
  directionLo := (186217061278036887783/100000000000000000000)
  directionHi := (23277132659754610973/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree015.table
  base := (-3945948071966150079596342233322784561129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-323172212946423140821350356497200000000000000)
      constant := (557581701384611803156879278778209942844659182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree015.table
  base := (-526374300135757887973893731918764865699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-18372212560476987556201676962900000000000000)
      constant := (32659308280970732904021316539025687190864552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186217061278036887783/100000000000000000000)
  centralHi := (23277132659754610973/12500000000000000000)
  directionLo := (192752970824876963617/100000000000000000000)
  directionHi := (96376485412438481809/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree016.table
  base := (-209162418454777127053278178602422955631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-3180447303212722650465060625995000000000000000)
      constant := (6109636302408036984346020860566196043651702050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree016.table
  base := (-683610167708814232057723859041114140623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-20078471539367184865998438165500000000000000)
      constant := (39770526325491037812499019218981717931896904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192752970824876963617/100000000000000000000)
  centralHi := (96376485412438481809/50000000000000000000)
  directionLo := (49768603062450172227/25000000000000000000)
  directionHi := (199074412249800688909/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree017.table
  base := (-6334509513781209158415177168862705752023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-3452344689907637033537968043515200000000000000)
      constant := (7363323666553269232576126176184716843727843106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree017.table
  base := (-6551619597375631038402814874059006161013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-21784730518257382175795199368100000000000000)
      constant := (47905479747749889683806782199413220565573203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/25000000000000000000)
  centralHi := (199074412249800688909/100000000000000000000)
  directionLo := (102600603632960317061/50000000000000000000)
  directionHi := (205201207265920634123/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree018.table
  base := (-7284447555801346307807395039785987903179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-413804675178061268512319495670600000000000000)
      constant := (974931611800948967992821942328793686089863082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree018.table
  base := (-7480916240310405178280059443410979551167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-23490989497147579485591960570700000000000000)
      constant := (57034451566030080484201073829370368994452377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102600603632960317061/50000000000000000000)
  centralHi := (205201207265920634123/100000000000000000000)
  directionLo := (211150300293840557703/100000000000000000000)
  directionHi := (26393787536730069713/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree019.table
  base := (-4048291369915403106352197789418313232863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-3996139463297465799683782878555600000000000000)
      constant := (10338891542750669854426949414491320655684219172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree019.table
  base := (-8274197358136764116359404556197498286081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-25197248476037776795388721773300000000000000)
      constant := (67133585466322431000357904421965624846355111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211150300293840557703/100000000000000000000)
  centralHi := (26393787536730069713/12500000000000000000)
  directionLo := (108468155655204593059/50000000000000000000)
  directionHi := (216936311310409186119/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree020.table
  base := (-4392685560401188580015745701720652172139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-4268036849992380182756690296075800000000000000)
      constant := (12053638741228772739353059995113594405134713716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree020.table
  base := (-8945730903243042144374029080431184645289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-26903507454927974105185482975900000000000000)
      constant := (78183348621807311586894552106889708220599359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108468155655204593059/50000000000000000000)
  centralHi := (216936311310409186119/100000000000000000000)
  directionLo := (11128597959284279629/5000000000000000000)
  directionHi := (222571959185685592581/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree021.table
  base := (-9362799189776183097573081792228068570731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-504437137409699396203288634844000000000000000)
      constant := (1546218640180946355313555635512265934280046698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree021.table
  base := (-4753683826947003244556263185705623164303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-28609766433818171414982244178500000000000000)
      constant := (90167517317040255910337432580738003776138386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11128597959284279629/5000000000000000000)
  centralHi := (222571959185685592581/100000000000000000000)
  directionLo := (57017097691472236303/25000000000000000000)
  directionHi := (228068390765888945213/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree022.table
  base := (-393556716608224293701912023672883928343/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-4811831623382208948902505131116200000000000000)
      constant := (15923649520268248784507657410744878703498653650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree022.table
  base := (-9969051079689736427852503063654269032597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-30316025412708368724779005381100000000000000)
      constant := (103072478942138755440093502360857305694374707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57017097691472236303/25000000000000000000)
  centralHi := (228068390765888945213/100000000000000000000)
  directionLo := (233435440148512887617/100000000000000000000)
  directionHi := (116717720074256443809/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree023.table
  base := (-5111111180278965214925614392541001343051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-5083729010077123331975412548636400000000000000)
      constant := (18074799998962320956941957909300633608281670644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree023.table
  base := (-2067836690112429689404234734527777378729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-32022284391598566034575766583700000000000000)
      constant := (116886730789566016506243904775557363842599995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233435440148512887617/100000000000000000000)
  centralHi := (116717720074256443809/50000000000000000000)
  directionLo := (119340917719068244159/50000000000000000000)
  directionHi := (238681835438136488319/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree024.table
  base := (-5259966201418435875588652224490660577029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-595069599641337523894257774017400000000000000)
      constant := (2263090887536511426208200446271402284121702764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree024.table
  base := (-1328112426895935316088779977603699677819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-33728543370488763344372527786300000000000000)
      constant := (131600505525311646573305100303684281128526312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119340917719068244159/50000000000000000000)
  centralHi := (238681835438136488319/100000000000000000000)
  directionLo := (48763073085647664861/20000000000000000000)
  directionHi := (121907682714119162153/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree025.table
  base := (-5369103904299881199405065673533582661021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-5627523783466952098121227383676800000000000000)
      constant := (22801337386159542646318611767698888209208169324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree025.table
  base := (-5416138810998721569034413944041612660647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-35434802349378960654169288988900000000000000)
      constant := (147205481479590502228487934931214064535148514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48763073085647664861/20000000000000000000)
  centralHi := (121907682714119162153/50000000000000000000)
  directionLo := (49768603062450172227/20000000000000000000)
  directionHi := (15552688457015678821/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree026.table
  base := (-10882317984822717951865469499710597775679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-5899421170161866481194134801197000000000000000)
      constant := (25374189555414791427371246137271583046505462738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree026.table
  base := (-10966509062366965180025948223625658130683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-37141061328269157963966050191500000000000000)
      constant := (163694552185292437586944593490056474019094973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/20000000000000000000)
  centralHi := (15552688457015678821/6250000000000000000)
  directionLo := (253771078179687058683/100000000000000000000)
  directionHi := (63442769544921764671/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree027.table
  base := (-10956779140746169012111946675513053039717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-685702061872975651585226913190800000000000000)
      constant := (3120596988860158329003629377321757346995293686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree027.table
  base := (-2758008473655562654010024395210761618033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-38847320307159355273762811394100000000000000)
      constant := (181061639065641502163438393924825869379651292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253771078179687058683/100000000000000000000)
  centralHi := (63442769544921764671/25000000000000000000)
  directionLo := (258605247377675161247/100000000000000000000)
  directionHi := (8081413980552348789/3125000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree028.table
  base := (-1096546710257592172776479958938639662157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-6443215943551695247339949636237400000000000000)
      constant := (30934027846155171971363987775411863730061448540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree028.table
  base := (-1379081803143285664903421857340037382811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-40553579286049552583559572596700000000000000)
      constant := (199301536763199388297673396842811910583453928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258605247377675161247/100000000000000000000)
  centralHi := (8081413980552348789/3125000000000000000)
  directionLo := (65837673401165370751/25000000000000000000)
  directionHi := (52670138720932296601/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree029.table
  base := (-5455855657622853560494461849688961865097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-6715113330246609630412857053757600000000000000)
      constant := (33919415997017519459731530090924912830965035068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree029.table
  base := (-10971629464027545292791950106151536977711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-42259838264939749893356333799300000000000000)
      constant := (218409783966954972341263093447078545877513641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65837673401165370751/25000000000000000000)
  centralHi := (52670138720932296601/20000000000000000000)
  directionLo := (268012129712153168409/100000000000000000000)
  directionHi := (26801212971215316841/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree030.table
  base := (-5399186949281153918961536248274983585977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-776334524104613779276196052364200000000000000)
      constant := (4115655844124662087159992318966015708948709532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree030.table
  base := (-2712938438873639610461527738217981203633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-43966097243829947203153095001900000000000000)
      constant := (238382554672059399592108761972518334928905692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268012129712153168409/100000000000000000000)
  centralHi := (26801212971215316841/10000000000000000000)
  directionLo := (54518773105649301597/20000000000000000000)
  directionHi := (136296932764123253993/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree031.table
  base := (-2656979142543437583893576838336402676539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-7258908103636438396558671888798000000000000000)
      constant := (40297941691651945933907078057661867148810134632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree031.table
  base := (-10675425215165791411267097141145169266187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-45672356222720144512949856204500000000000000)
      constant := (259216566132030989213373461211972263274589997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54518773105649301597/20000000000000000000)
  centralHi := (136296932764123253993/50000000000000000000)
  directionLo := (277099854518943160901/100000000000000000000)
  directionHi := (138549927259471580451/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree032.table
  base := (-10402457557529892164877259275255243685159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-7530805490331352779631579306318200000000000000)
      constant := (43690063504360106400201791056692442565992807298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree032.table
  base := (-10444702064859483772876591076577110564389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-47378615201610341822746617407100000000000000)
      constant := (280909000641200571231233307952165935637351459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277099854518943160901/100000000000000000000)
  centralHi := (138549927259471580451/50000000000000000000)
  directionLo := (70383433431280185901/25000000000000000000)
  directionHi := (56306746745024148721/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree033.table
  base := (-10123820151862188282095201344145852142989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-866966986336251906967165191537600000000000000)
      constant := (5246318185484856729559323743359507911492465062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree033.table
  base := (-1270168939115137494947842651008552847099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-49084874180500539132543378609700000000000000)
      constant := (303457438891343204837037046966554329218571752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/25000000000000000000)
  centralHi := (56306746745024148721/20000000000000000000)
  directionLo := (14294942906146469971/5000000000000000000)
  directionHi := (285898858122929399421/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree034.table
  base := (-76512298635625504040859553292126429817/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-8074600263721181545777394141358600000000000000)
      constant := (50877994023548331949677286961682084434949807872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree034.table
  base := (-982689130930596972517911322019661033597/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-50791133159390736442340139812300000000000000)
      constant := (326859803082770043597841286832950840450057070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14294942906146469971/5000000000000000000)
  centralHi := (285898858122929399421/100000000000000000000)
  directionLo := (290198330330797455631/100000000000000000000)
  directionHi := (18137395645674840977/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree035.table
  base := (-2353267947165470201160126677688076013141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-8346497650416095928850301558878800000000000000)
      constant := (54673154720698616361609688694024525511830461208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree035.table
  base := (-9442625266192511410814139738331602008077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-52497392138280933752136901014900000000000000)
      constant := (351114308296608832804613823287224036850942587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290198330330797455631/100000000000000000000)
  centralHi := (18137395645674840977/6250000000000000000)
  directionLo := (147217513205435550819/50000000000000000000)
  directionHi := (294435026410871101639/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree036.table
  base := (-1796695495969717153668637567483991878389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-957599448567890034658134330711000000000000000)
      constant := (6511343052190027464210442202977897360663691310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree036.table
  base := (-2252418412610152047527507509908992483093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-54203651117171131061933662217500000000000000)
      constant := (376219420887528392392665851828938357162582732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147217513205435550819/50000000000000000000)
  centralHi := (294435026410871101639/100000000000000000000)
  directionLo := (149305809187350516681/50000000000000000000)
  directionHi := (298611618374701033363/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree037.table
  base := (-8505794730204292570987697432812770810013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59940000000000000000000000000000000000000000
      center := (233235)
      previous := (192339)
      next := (0)
      square := (8129822193535646005502215141800000000000000)
      linear := (-240278173616376343108003145781600000000000000)
      constant := (1693637019772970171609298660669470251764782078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree037.table
  base := (-8528999207625879831451531836257981635841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1420)
      previous := (1207)
      next := (0)
      square := (50184087614417567935198858900000000000000)
      linear := (-1511078651244900766803524957300000000000000)
      constant := (10869562779914478348623747374058454679473883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149305809187350516681/50000000000000000000)
  centralHi := (298611618374701033363/100000000000000000000)
  directionLo := (302730593893557134941/100000000000000000000)
  directionHi := (151365296946778567471/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree038.table
  base := (-3990444117365564102126710007266287406529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-9162189810500839078069023811439400000000000000)
      constant := (66860409736039382156599230008387794623109622876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree038.table
  base := (-4000714729231500593897111831466319250711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-57616169074951525681527184622700000000000000)
      constant := (428976381328672362450156039306845217891553282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302730593893557134941/100000000000000000000)
  centralHi := (151365296946778567471/50000000000000000000)
  directionLo := (306794273626372526433/100000000000000000000)
  directionHi := (153397136813186263217/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree039.table
  base := (-1852375814857628698547923097777653360123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1048231910799528162349103469884400000000000000)
      constant := (7909938022158382355865345015881202263599396136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree039.table
  base := (-7427675810473868581405166941626694775141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-59322428053841722991323945825300000000000000)
      constant := (456626122386140906980714404142313054852831971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306794273626372526433/100000000000000000000)
  centralHi := (153397136813186263217/50000000000000000000)
  directionLo := (3108048265080857167/1000000000000000000)
  directionHi := (310804826508085716701/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree040.table
  base := (-3396141118882378902355870740518504434217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-9705984583890667844214838646479800000000000000)
      constant := (75651524644149670306935815320870574247176444348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree040.table
  base := (-170208748654348728578155400532278528397/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-61028687032731920301120707027900000000000000)
      constant := (485122208635877657988631248742852427784980280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3108048265080857167/1000000000000000000)
  centralHi := (310804826508085716701/100000000000000000000)
  directionLo := (314764283284347537269/100000000000000000000)
  directionHi := (31476428328434753727/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree041.table
  base := (-6129779042058209246652484585186558820717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-9977881970585582227287746064000000000000000000)
      constant := (80246534233515719328782527141053645357859025174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree041.table
  base := (-6143977880575295118784215229265120467577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-62734946011622117610917468230500000000000000)
      constant := (514463919963331115949369623224336050079887087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314764283284347537269/100000000000000000000)
  centralHi := (31476428328434753727/10000000000000000000)
  directionLo := (63734909706469879371/20000000000000000000)
  directionHi := (39834318566543674607/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree042.table
  base := (-5422471259397704691258206333047239208573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1138864373031166290040072609057800000000000000)
      constant := (9441596116579404894334313960769049931422344134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree042.table
  base := (-543501202301697207931764358709618580633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-64441204990512314920714229433100000000000000)
      constant := (544650637020116100096314749806265321631134230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63734909706469879371/20000000000000000000)
  centralHi := (39834318566543674607/12500000000000000000)
  directionLo := (20158588210607931293/6250000000000000000)
  directionHi := (322537411369726900689/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree043.table
  base := (-467077075397704437844846614674846599347/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-10521676743975410993433560899040400000000000000)
      constant := (89834925748829271838005830788952968708900210340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree043.table
  base := (-4681841529377649526636067207442692535457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-66147463969402512230510990635700000000000000)
      constant := (575681827051834711881352432480410953918959367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20158588210607931293/6250000000000000000)
  centralHi := (322537411369726900689/100000000000000000000)
  directionLo := (326354555022405287783/100000000000000000000)
  directionHi := (40794319377800660973/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree044.table
  base := (-968758189337392621183966487374392197979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-10793574130670325376506468316560600000000000000)
      constant := (94828137549816165574550930737823128188466453352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree044.table
  base := (-485600148642282376346044843179750336827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-67853722948292709540307751838300000000000000)
      constant := (607557031731687556012493144581895374311070696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326354555022405287783/100000000000000000000)
  centralHi := (40794319377800660973/12500000000000000000)
  directionLo := (165063782698279913367/50000000000000000000)
  directionHi := (66025513079311965347/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree045.table
  base := (-151778184677629202288313707895086265143/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1229496835262804417731041748231200000000000000)
      constant := (11105992499340575634395628454203735685086923880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree045.table
  base := (-1522089528183319402465932893779406141723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-69559981927182906850104513040900000000000000)
      constant := (640275856713655761893702337264831985983962426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165063782698279913367/50000000000000000000)
  centralHi := (66025513079311965347/20000000000000000000)
  directionLo := (33385793877852838887/10000000000000000000)
  directionHi := (333857938778528388871/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree046.table
  base := (-2152627916611272433890346845087105033907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-11337368904060154142652283151601000000000000000)
      constant := (105212251953669319237969823036398672019790173354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree046.table
  base := (-1080111501763056243333547892406766407821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-71266240906073104159901274243500000000000000)
      constant := (673837962660337039547327055828790273575386102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33385793877852838887/10000000000000000000)
  centralHi := (333857938778528388871/100000000000000000000)
  directionLo := (84386772192178961207/25000000000000000000)
  directionHi := (337547088768715844829/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree047.table
  base := (-1226453512747056238658379430025595096977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-11609266290755068525725190569121200000000000000)
      constant := (110603045344122566944269146166089533570582634894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree047.table
  base := (-246629270253309391491509008381520601941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-72972499884963301469698035446100000000000000)
      constant := (708243057535761721185236393832628491479713855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84386772192178961207/25000000000000000000)
  centralHi := (337547088768715844829/100000000000000000000)
  directionLo := (341196352540620016363/100000000000000000000)
  directionHi := (85299088135155004091/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree048.table
  base := (-128618649032034813747093347469655572577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1320129297494442545422010887404600000000000000)
      constant := (12902918779549220129008411853570505494761115132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree048.table
  base := (-263132705371593764301884660718274470871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-74678758863853498779494796648700000000000000)
      constant := (743490889983611987839589170537876682249377601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341196352540620016363/100000000000000000000)
  centralHi := (85299088135155004091/25000000000000000000)
  directionLo := (344806996503566881663/100000000000000000000)
  directionHi := (2693804660184116263/781250000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree049.table
  base := (377425437985256072506248152527500527607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-12153061064144897291871005404161600000000000000)
      constant := (121781885299811874694777102323480038024023250492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree049.table
  base := (374829943375995790132168816397938923391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-76385017842743696089291557851300000000000000)
      constant := (779581243636987991213724221107697556772244558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344806996503566881663/100000000000000000000)
  centralHi := (2693804660184116263/781250000000000000)
  directionLo := (348380221437151205589/100000000000000000000)
  directionHi := (34838022143715120559/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree050.table
  base := (1809664412755554773160118887451588552221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-12424958450839811674943912821681800000000000000)
      constant := (127569861683828241181323454582861238405934468938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree050.table
  base := (1805095363721854620205269048744122195401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-78091276821633893399088319053900000000000000)
      constant := (816513932227857288057328463072730703285503969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348380221437151205589/100000000000000000000)
  centralHi := (34838022143715120559/10000000000000000000)
  directionLo := (70383433431280185901/20000000000000000000)
  directionHi := (175958583578200464753/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree051.table
  base := (2907076773562301466678971219552986834097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1410761759726080673112980026578000000000000000)
      constant := (14832241122720654933031369750333574701565818274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree051.table
  base := (2903056579386419570308992503649624699539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-79797535800524090708885080256500000000000000)
      constant := (854288795383138371120446781945696336213668891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/20000000000000000000)
  centralHi := (175958583578200464753/50000000000000000000)
  directionLo := (88854729189761601337/25000000000000000000)
  directionHi := (355418916759046405349/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree052.table
  base := (505872340252839816678726995960846715517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-12968753224229640441089727656722200000000000000)
      constant := (139542786335561604566478466056515637302991433808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree052.table
  base := (808688532554853460803457161007585535451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-81503794779414288018681841459100000000000000)
      constant := (892905695010471367618820971545096922990162095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88854729189761601337/25000000000000000000)
  centralHi := (355418916759046405349/100000000000000000000)
  directionLo := (358886500499756444103/100000000000000000000)
  directionHi := (44860812562469555513/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree053.table
  base := (522927594879190258580885902363909360323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-13240650610924554824162635074242400000000000000)
      constant := (145727689461317477705415875243670180901137142940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree053.table
  base := (5226166748041136472290956135558316632599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-83210053758304485328478602661700000000000000)
      constant := (932364512190515483765616376903979335470028031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358886500499756444103/100000000000000000000)
  centralHi := (44860812562469555513/12500000000000000000)
  directionLo := (72464179866124037177/20000000000000000000)
  directionHi := (181160449665310092943/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree054.table
  base := (806735877956416253883818106446126727473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1501394221957718800803949165751400000000000000)
      constant := (16893873491369167787638070166537563638547117328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree054.table
  base := (1612788505573608255210362093475764795987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-84916312737194682638275363864300000000000000)
      constant := (972665144504420758300511966061273288022824812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72464179866124037177/20000000000000000000)
  centralHi := (181160449665310092943/50000000000000000000)
  directionLo := (365723048142357486457/100000000000000000000)
  directionHi := (182861524071178743229/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree055.table
  base := (7720741629684197735332965322125876065241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-13784445384314383590308449909282800000000000000)
      constant := (158494286623831526951032673000908182541997018498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree055.table
  base := (7718340046565016823606473409403096284731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-86622571716084879948072125066900000000000000)
      constant := (1013807503735238438390928465224472838813796739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365723048142357486457/100000000000000000000)
  centralHi := (182861524071178743229/50000000000000000000)
  directionLo := (73818767747321509021/20000000000000000000)
  directionHi := (184546919368303772553/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree056.table
  base := (1805955808096228761360535692487910161811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-14056342771009297973381357326803000000000000000)
      constant := (165075951598062912830647833776021318699330599790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree056.table
  base := (2256917327882360880721539215300474278093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-88328830694975077257868886269500000000000000)
      constant := (1055791513890704728711174746366185397146837268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73818767747321509021/20000000000000000000)
  centralHi := (184546919368303772553/50000000000000000000)
  directionLo := (186217061278036887783/50000000000000000000)
  directionHi := (372434122556073775567/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree057.table
  base := (1038094680677201217189864936785157960391/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1592026684189356928494918304924800000000000000)
      constant := (19087760523658047894877939896121348624599550220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree057.table
  base := (5189546997507699204158640072587494263973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-90035089673865274567665647472100000000000000)
      constant := (1098617109502265730422763563244744559294758074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186217061278036887783/50000000000000000000)
  centralHi := (372434122556073775567/100000000000000000000)
  directionLo := (187872356598103799981/50000000000000000000)
  directionHi := (375744713196207599963/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree058.table
  base := (470967984942137876711601512217909352453/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-14600137544399126739527172161843400000000000000)
      constant := (178635955920757047353157750782945387509208035850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree058.table
  base := (5886286446489523122834327057081856169033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-91741348652755471877462408674700000000000000)
      constant := (1142284234161585433090032417917690122190812354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187872356598103799981/50000000000000000000)
  centralHi := (375744713196207599963/100000000000000000000)
  directionLo := (473782985899280207/125000000000000000)
  directionHi := (379026388719424165601/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree059.table
  base := (6604749176400590765852534088467984500781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-14872034931094041122600079579363600000000000000)
      constant := (185614276541614015949747210080943055333228417236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree059.table
  base := (6604035249818350115151245175822990564217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-93447607631645669187259169877300000000000000)
      constant := (1186792839261245969477432178042803348164826146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473782985899280207/125000000000000000)
  centralHi := (379026388719424165601/100000000000000000000)
  directionLo := (382279893790499731317/100000000000000000000)
  directionHi := (191139946895249865659/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree060.table
  base := (3671702295078149536084366194178056618757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1682659146420995056185887444098200000000000000)
      constant := (21413866564027456517538981082849742684797639976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree060.table
  base := (14685556215859653962579025721354451221807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-95153866610535866497055931079900000000000000)
      constant := (1232142882911040140523856007886534243722653783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382279893790499731317/100000000000000000000)
  centralHi := (191139946895249865659/50000000000000000000)
  directionLo := (192752970824876963617/50000000000000000000)
  directionHi := (77101188329950785447/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree061.table
  base := (16206102888198878258084952435014636377379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-15415829704483869888745894414404000000000000000)
      constant := (199967517044771379088707372394459826026502359862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree061.table
  base := (16205003667881490039525724346003012630847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-96860125589426063806852692282500000000000000)
      constant := (1278334329005281720804634505832878124291629543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192752970824876963617/50000000000000000000)
  centralHi := (77101188329950785447/20000000000000000000)
  directionLo := (97176303984707096249/25000000000000000000)
  directionHi := (388705215938828384997/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree062.table
  base := (2220919278388114376853436749388662128549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-15687727091178784271818801831924200000000000000)
      constant := (207342424847435350353536692426833349676362720976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree062.table
  base := (17766390120891175492271714042246753591793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-98566384568316261116649453485100000000000000)
      constant := (1325367146420014406185383447862835805667164617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97176303984707096249/25000000000000000000)
  centralHi := (388705215938828384997/100000000000000000000)
  directionLo := (195939186196150493899/50000000000000000000)
  directionHi := (391878372392300987799/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree063.table
  base := (4842635343609369114820297859222462369347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1773291608652633183876856583271600000000000000)
      constant := (23872168627163104517306648611962789670821795096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree063.table
  base := (19369695974252233802919550133712440792671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-100272643547206458426446214687700000000000000)
      constant := (1373241308321966860313101232214452331445166599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195939186196150493899/50000000000000000000)
  centralHi := (391878372392300987799/100000000000000000000)
  directionLo := (197513020203496112253/50000000000000000000)
  directionHi := (395026040406992224507/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree064.table
  base := (10507822733388985597773508847587434050193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-16231521864568613037964616666964600000000000000)
      constant := (222488791252377901632777113212493291897567406308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree064.table
  base := (5253726081737282292203660335731169880677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-101978902526096655736242975890300000000000000)
      constant := (1421956791573648814673953723428863886266587252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197513020203496112253/50000000000000000000)
  centralHi := (395026040406992224507/100000000000000000000)
  directionLo := (49768603062450172227/12500000000000000000)
  directionHi := (398148824499601377817/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree065.table
  base := (22702650196288541720726527227145317525961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-16503419251263527421037524084484800000000000000)
      constant := (230260242054445568923310708085722584230272578658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree065.table
  base := (22702000603460273391345768276170098965053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-103685161504986853046039737092900000000000000)
      constant := (1471513576221171215024042162156076865483157557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/12500000000000000000)
  centralHi := (398148824499601377817/100000000000000000000)
  directionLo := (100311826415558457011/25000000000000000000)
  directionHi := (80249461132446765609/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree066.table
  base := (24431541462325983487876475198942835150297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1863924070884271311567825722445000000000000000)
      constant := (26462651880384277101038738130509949343773618674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree066.table
  base := (4886194446326015233803557324200774202287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-105391420483877050355836498295500000000000000)
      constant := (1521911645053253058240619695832354299414654515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100311826415558457011/25000000000000000000)
  centralHi := (80249461132446765609/20000000000000000000)
  directionLo := (101080510656107017063/25000000000000000000)
  directionHi := (404322042624428068253/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree067.table
  base := (26202307070688835044709267037722266170911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-17047214024653356187183338919525200000000000000)
      constant := (246199663155011064872925480329917718746852299758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree067.table
  base := (13100904182646082783813048530392740093151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-107097679462767247665633259498100000000000000)
      constant := (1573150983221492581145760227993215322375047438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101080510656107017063/25000000000000000000)
  centralHi := (404322042624428068253/100000000000000000000)
  directionLo := (203686786514723109767/50000000000000000000)
  directionHi := (81474714605889243907/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree068.table
  base := (5602987294793223070817420015691679821773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-17319111411348270570256246337045400000000000000)
      constant := (254367628409919569261586871952263146837565861970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree068.table
  base := (28014499645409694569369663646972724890077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-108803938441657444975430020700700000000000000)
      constant := (1625231577913368340172094140425105660374515413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203686786514723109767/50000000000000000000)
  centralHi := (81474714605889243907/20000000000000000000)
  directionLo := (82080482906368253649/20000000000000000000)
  directionHi := (205201207265920634123/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree069.table
  base := (233354848026210762431938285981317739311/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-1954556533115909439258794861618400000000000000)
      constant := (29185306740500386812471072259193358861709012736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree069.table
  base := (29869037994369998013555632782443108782639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-110510197420547642285226781903300000000000000)
      constant := (1678153418070628596714632916553564615923432791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82080482906368253649/20000000000000000000)
  centralHi := (205201207265920634123/50000000000000000000)
  directionLo := (413409065822646179727/100000000000000000000)
  directionHi := (25838066613915386233/6250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree070.table
  base := (31765751395089098073894302048821231187003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-17862906184738099336402061172085800000000000000)
      constant := (271100058167655537291244523681309475010191151334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree070.table
  base := (31765416438819900874571310548508150056107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-112216456399437839595023543105900000000000000)
      constant := (1731916494146752854163312778403907657426810483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413409065822646179727/100000000000000000000)
  centralHi := (25838066613915386233/6250000000000000000)
  directionLo := (208197003793967173359/50000000000000000000)
  directionHi := (416394007587934346719/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree071.table
  base := (33703922183287199315116587764170520670449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-18134803571433013719474968589606000000000000000)
      constant := (279664519403771215240136375286914359733250838322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree071.table
  base := (6740725791414393445998982643975971784859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-113922715378328036904820304308500000000000000)
      constant := (1786520797898051012740338304056215526867359855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208197003793967173359/50000000000000000000)
  centralHi := (416394007587934346719/100000000000000000000)
  directionLo := (419357703405968746219/100000000000000000000)
  directionHi := (20967885170298437311/5000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree072.table
  base := (35683926995606572647430901901156714624751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2045188995347547566949764000791800000000000000)
      constant := (32040127006748429101783228343460303761783114142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree072.table
  base := (7136734069533145852289079975017378154559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-115628974357218234214617065511100000000000000)
      constant := (1841966322203723692002345848488993953467956355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419357703405968746219/100000000000000000000)
  centralHi := (20967885170298437311/5000000000000000000)
  directionLo := (211150300293840557703/50000000000000000000)
  directionHi := (422300600587681115407/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree073.table
  base := (37705760708582595991229834635171472694451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-18678598344822842485620783424646400000000000000)
      constant := (297189928002277740363411390957912608871229953878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree073.table
  base := (7541107223228831021076243119434843605371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-117335233336108431524413826713700000000000000)
      constant := (1898253060910859215328147023020931504478764495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211150300293840557703/50000000000000000000)
  centralHi := (422300600587681115407/100000000000000000000)
  directionLo := (425223130964795823037/100000000000000000000)
  directionHi := (212611565482397911519/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree074.table
  base := (39769418883963029248460854569049652014249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59940000000000000000000000000000000000000000
      center := (233235)
      previous := (192339)
      next := (0)
      square := (8129822193535646005502215141800000000000000)
      linear := (-512175560311290726180910563301800000000000000)
      constant := (8274347925515949872371824015649283614173408506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree074.table
  base := (9942305594378802541345666951697399344997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1420)
      previous := (1207)
      next := (0)
      square := (50184087614417567935198858900000000000000)
      linear := (-3217337630135098076600286159900000000000000)
      constant := (52848135370294688847439007257051215103059556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425223130964795823037/100000000000000000000)
  centralHi := (212611565482397911519/50000000000000000000)
  directionLo := (428125711629530170359/100000000000000000000)
  directionHi := (10703142790738254259/2500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree075.table
  base := (41874897675714773477249854017533556732533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2135821457579185694640733139965200000000000000)
      constant := (35027108659245283115772932455583811905003078186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree075.table
  base := (41874725772220701707848821067509998632549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-120747751293888826144007349118900000000000000)
      constant := (2013350160974621342231334904346421188127959581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428125711629530170359/100000000000000000000)
  centralHi := (10703142790738254259/2500000000000000000)
  directionLo := (431008745629458602079/100000000000000000000)
  directionHi := (2693804660184116263/625000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree076.table
  base := (44022193749698942890853262904688946280527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-19494290504907585634839505677207000000000000000)
      constant := (324469241330191294843995686037304505128202717006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree076.table
  base := (880440867874754214808641595094130372913/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-122454010272779023453804110321500000000000000)
      constant := (2072160513752982903855898072117393224025894850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431008745629458602079/100000000000000000000)
  centralHi := (2693804660184116263/625000000000000000)
  directionLo := (108468155655204593059/25000000000000000000)
  directionHi := (433872622620818372237/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree077.table
  base := (46211304214284530653417899746374895545779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-19766187891602500017912413094727200000000000000)
      constant := (333826662793741244249833523506984281584351775062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree077.table
  base := (23105586363099356401811989014370576535313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-124160269251669220763600871524100000000000000)
      constant := (2131812063591765531243865682089346638553686994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108468155655204593059/25000000000000000000)
  centralHi := (433872622620818372237/100000000000000000000)
  directionLo := (43671771948325476543/10000000000000000000)
  directionHi := (436717719483254765431/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree078.table
  base := (48442226560407686365538010618110947526067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2226453919810823822331702279138600000000000000)
      constant := (38146249085266914849510055023936689968937343014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree078.table
  base := (24221055795320450602284757348382070634701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-125866528230559418073397632726700000000000000)
      constant := (2192304807507969142032719237629270109397811338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43671771948325476543/10000000000000000000)
  centralHi := (436717719483254765431/100000000000000000000)
  directionLo := (439544400898751665129/100000000000000000000)
  directionHi := (43954440089875166513/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree079.table
  base := (10142991721957572677636000814283521783291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-20309982664992328784058227929767600000000000000)
      constant := (352937977768079559958755009318381404470273556990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree079.table
  base := (12678714524672086942110760990678048102541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-127572787209449615383194393929300000000000000)
      constant := (2253638742916407090551122429642352991409514516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439544400898751665129/100000000000000000000)
  centralHi := (43954440089875166513/10000000000000000000)
  directionLo := (22117650994863256967/5000000000000000000)
  directionHi := (442353019897265139341/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree080.table
  base := (53029498470188315516068211446964204761047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-20581880051687243167131135347287800000000000000)
      constant := (362691870376116742089413438571908827403495481566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree080.table
  base := (1657169081644901430228151864637870554011/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-129279046188339812692991155131900000000000000)
      constant := (2315813867575062317788520324398055833230113888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22117650994863256967/5000000000000000000)
  centralHi := (442353019897265139341/100000000000000000000)
  directionLo := (445143918371371185161/100000000000000000000)
  directionHi := (222571959185685592581/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree081.table
  base := (13846461124190120680315937282692775471839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2317086382042461950022671418312000000000000000)
      constant := (41397546580746950676854394805096811492708226552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree081.table
  base := (55385767711054340225341066384295123912961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-130985305167230010002787916334500000000000000)
      constant := (2378830179537994340483040127053300024636843609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445143918371371185161/100000000000000000000)
  centralHi := (222571959185685592581/50000000000000000000)
  directionLo := (447917427562051550043/100000000000000000000)
  directionHi := (111979356890512887511/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree082.table
  base := (2311359810345721153925133788450863606509/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-21125674825077071933276950182328200000000000000)
      constant := (382596124002563436555658208561376390723108825050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree082.table
  base := (57783928159132996763276001577197351782139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-132691564146120207312584677537100000000000000)
      constant := (2442687677114751233369437027600183174589748291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447917427562051550043/100000000000000000000)
  centralHi := (111979356890512887511/25000000000000000000)
  directionLo := (14083558391174112781/3125000000000000000)
  directionHi := (450673868517571608993/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree083.table
  base := (60223949510099544980652603112613404197879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-21397572211771986316349857599848400000000000000)
      constant := (392746484427362454184744672897291725556197208862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree083.table
  base := (60223890883134972188322573121429060235321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-134397823125010404622381438739700000000000000)
      constant := (2507386358835385889116790972918636383462154449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14083558391174112781/3125000000000000000)
  centralHi := (450673868517571608993/100000000000000000000)
  directionLo := (453413552527249836849/100000000000000000000)
  directionHi := (9068271050544996737/2000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree084.table
  base := (62705706165576679923672574908662827776339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2407718844274100077713640557485400000000000000)
      constant := (44781000028929750873065319541976469402064545638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree084.table
  base := (31352827474182609507747398985909874561061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-136104082103900601932178199942300000000000000)
      constant := (2572926223420300787718156152219821236548185018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453413552527249836849/100000000000000000000)
  centralHi := (9068271050544996737/2000000000000000000)
  directionLo := (18245471261271115617/4000000000000000000)
  directionHi := (228068390765888945213/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree085.table
  base := (32614632139074416212108189606495921126849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-21941366985161815082495672434888800000000000000)
      constant := (413443671291572081579506219703635654791340635044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree085.table
  base := (16307304885045809499761295053652166414119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-137810341082790799241974961144900000000000000)
      constant := (2639307269754253085706104243597799263283715644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18245471261271115617/4000000000000000000)
  centralHi := (228068390765888945213/50000000000000000000)
  directionLo := (114710962127905575617/25000000000000000000)
  directionHi := (458843848511622302469/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree086.table
  base := (67794623020888373606657066202697011892783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-22213264371856729465568579852409000000000000000)
      constant := (423990497337581069673720910697010137903557628174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree086.table
  base := (67794583947633355795720471069521060347977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-139516600061680996551771722347500000000000000)
      constant := (2706529496863944466273721549472374331616380513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114710962127905575617/25000000000000000000)
  centralHi := (458843848511622302469/100000000000000000000)
  directionLo := (115383759463730510119/25000000000000000000)
  directionHi := (461535037854922040477/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree087.table
  base := (70401781670763245058623344830854999628149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2498351306505738205404609696658800000000000000)
      constant := (48296608693115790921072563185789678900836847658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree087.table
  base := (35200873774665685012403272151206403206879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-141222859040571193861568483550100000000000000)
      constant := (2774592903898699956361810431029003131980434702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115383759463730510119/25000000000000000000)
  centralHi := (461535037854922040477/100000000000000000000)
  directionLo := (232105312853094794017/50000000000000000000)
  directionHi := (92842125141237917607/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree088.table
  base := (18262684898679515691409402341346087033517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-22757059145246558231714394687449400000000000000)
      constant := (445480613852557470471339879184877009960477332904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree088.table
  base := (18262677450323894908823569032867295702817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-142929118019461391171365244752700000000000000)
      constant := (2843497490113808607231539397810381311268625892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232105312853094794017/50000000000000000000)
  centralHi := (92842125141237917607/20000000000000000000)
  directionLo := (233435440148512887617/50000000000000000000)
  directionHi := (93374176059405155047/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree089.table
  base := (75741496237641726666788865738493820765303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-23028956531941472614787302104969600000000000000)
      constant := (456423904058015696669472623792953232581687368734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree089.table
  base := (4733841889153339394912668870648031616763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-144635376998351588481162005955300000000000000)
      constant := (2913243254856158092034461109243074484533576752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233435440148512887617/50000000000000000000)
  centralHi := (93374176059405155047/20000000000000000000)
  directionLo := (469516062259969435097/100000000000000000000)
  directionHi := (234758031129984717549/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree090.table
  base := (3138962044478600210386522007163819843891/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2588983768737376333095578835832200000000000000)
      constant := (51944372082920518651100990695701271214829050550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree090.table
  base := (3138961136223688851829980844074761346993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-146341635977241785790958767157900000000000000)
      constant := (2983830197551846223404148795809458707100835425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469516062259969435097/100000000000000000000)
  centralHi := (234758031129984717549/50000000000000000000)
  directionLo := (29509151557907581619/6250000000000000000)
  directionHi := (94429284985304261181/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree091.table
  base := (81248403788666510260345437677830491099799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-23572751305331301380933116940010000000000000000)
      constant := (478706947822216878591818716706826040655131222622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree091.table
  base := (20312095992388593661984690756195315898701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-148047894956131983100755528360500000000000000)
      constant := (3055258317695496277169770773729125549861286676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29509151557907581619/6250000000000000000)
  centralHi := (94429284985304261181/20000000000000000000)
  directionLo := (237381107305153364539/50000000000000000000)
  directionHi := (474762214610306729079/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree092.table
  base := (84064553889495653458596099357915370313761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-23844648692026215764006024357530200000000000000)
      constant := (490046701201924669913111434183061754997445287058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree092.table
  base := (21016134148126344688629826660691645593343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-149754153935022180410552289563100000000000000)
      constant := (3127527614841040806922655658275947451269146268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237381107305153364539/50000000000000000000)
  centralHi := (474762214610306729079/100000000000000000000)
  directionLo := (477363670876272976637/100000000000000000000)
  directionHi := (238681835438136488319/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree093.table
  base := (2716328158757726205895147419399116808509/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2679616230969014460786547975005600000000000000)
      constant := (55724289867920964645150784349920607164648920896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree093.table
  base := (86922485986126300726337649379917339131307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-151460412913912377720349050765700000000000000)
      constant := (3200638088593771193537552304423506837270759283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477363670876272976637/100000000000000000000)
  centralHi := (238681835438136488319/50000000000000000000)
  directionLo := (239975513398376956951/50000000000000000000)
  directionHi := (479951026796753913903/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree094.table
  base := (5613890316559052992063455142163646637981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-24388443465416044530151839192570600000000000000)
      constant := (513122670584667856289702517150251107585250403488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree094.table
  base := (89822231894603250386061702897422607884621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-153166671892802575030145811968300000000000000)
      constant := (3274589738603478221361693083235971550194046149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239975513398376956951/50000000000000000000)
  centralHi := (479951026796753913903/100000000000000000000)
  directionLo := (15078890912349270401/3125000000000000000)
  directionHi := (482524509195176652833/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree095.table
  base := (46381892790404810708233471803533105708701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-24660340852110958913224746610090800000000000000)
      constant := (524858886463783623373301082885377680235728580756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree095.table
  base := (23190943522575956950969105573709770987271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-154872930871692772339942573170900000000000000)
      constant := (3349382564558533134891161198244634705926295996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15078890912349270401/3125000000000000000)
  centralHi := (482524509195176652833/100000000000000000000)
  directionLo := (97016867775626284203/20000000000000000000)
  directionHi := (60635542359766427627/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree096.table
  base := (23936780598476954216649995413361459791717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (958855)
      previous := (790727)
      next := (0)
      square := (33422602351202100244842440027400000000000000)
      linear := (-2770248693200652588477517114179000000000000000)
      constant := (59636361821861625060635805700521812368749961256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree096.table
  base := (95747112370045791467139846636669309178479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-156579189850582969649739334373500000000000000)
      constant := (3425016566180779445495149804928800284265337751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97016867775626284203/20000000000000000000)
  centralHi := (60635542359766427627/12500000000000000000)
  directionLo := (48763073085647664861/10000000000000000000)
  directionHi := (487630730856476648611/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree097.table
  base := (6173265955961564899882374584508055745459/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-25204135625500787679370561445131200000000000000)
      constant := (548727780337261552609623436730005191393862497632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree097.table
  base := (19754449310375256781834519863901064707591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-158285448829473166959536095576100000000000000)
      constant := (3501491743221123691301774836718402787923460395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell027.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48763073085647664861/10000000000000000000)
  centralHi := (487630730856476648611/100000000000000000000)
  directionLo := (122540973639026472201/25000000000000000000)
  directionHi := (98032778911221177761/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree098.table
  base := (101839184098207550318013949025852013082373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (8629695)
      previous := (7116543)
      next := (0)
      square := (300803421160818902203581960246600000000000000)
      linear := (-25476033012195702062443468862651400000000000000)
      constant := (560860458243824436730480926133540207757382519194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree098.table
  base := (50919588236145618992559199593163477255531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (52540)
      previous := (44659)
      next := (0)
      square := (1856811241733450013602357779300000000000000)
      linear := (-159991707808363364269332856778700000000000000)
      constant := (3578808095455728804389728044709481600725643878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell027.Kernel098
