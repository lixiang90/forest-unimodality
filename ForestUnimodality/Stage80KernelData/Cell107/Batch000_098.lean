import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell107.Parameters
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch000_049
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch050_099
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch000_049
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel000
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
  base := (3587658319436027170134195737/100000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (323442563900712548585758550000000000000)
      linear := (-14875549801396459673186179000000000000)
      constant := (89691457985900679253354893425000000000000) }

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
  base := (3587658319436027170134195737/100000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (323442563900712548585758550000000000000)
      linear := (-14875549801396459673186179000000000000)
      constant := (89691457985900679253354893425000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel001
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
  base := (203061017585498609776898218534811086301139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-10138276121767350168090988804796046000000000000)
      constant := (1473200280399450964741840335353259837914058346859) }

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
  base := (202887672379759169861516636111339328590251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-10149155921010560386444042258021671000000000000)
      constant := (1471950894224474705984587573174583030882809401731) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel002
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
  base := (59635710999070971989008696398624475793387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-9922834099264617695709700955413848000000000000)
      constant := (437103199670226265863297973945684894842771886147) }

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
  base := (119085908848072161092878714451114577801779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-19867427797015655828125508817278946000000000000)
      constant := (872886068367973551178825068245941707849604394699) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel003
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
  base := (36582363146652825776398132368525614592343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-1641836681960617811930434167603297000000000000)
      constant := (30728979193153300593572080450403215669030508887) }

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
  base := (36506496576771798722214900135704730233219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-1643649981834486181655943076474234500000000000)
      constant := (30670797791590316387943008692183358210095106371) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel004
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
  base := (46958384796678699416989829666873682111547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-39260452352053005838076228122890996000000000000)
      constant := (381173992176216067445013235212609882410807481107) }

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
  base := (9369004096609011079355883982741114423357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-39303971549025846711488441935793496000000000000)
      constant := (380444301816353107921415591235497736577828358585) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel005
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
  base := (1961866383538547680409695458590647489549/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-12241961107203722765351160307230661500000000000)
      constant := (72822256383308046512853802344652786511817128276) }

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
  base := (31307423234011003186998979128604345994073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-49022243425030942153169908495050771000000000000)
      constant := (290834287993961940478005452960804591627255742113) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel006
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
  base := (5403019908230821227919617930621597751081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-1629867680710466007909251509304286000000000000)
      constant := (6899074927212758954496153047385607269899532329) }

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
  base := (21551698228060541809824257053155140196619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-6526723922337337510539041672700894000000000000)
      constant := (27570441681863033527022665141817815073461416971) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel007
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
  base := (15073864471364578372527239934217136808183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-68382628582338661508061467440985946000000000000)
      constant := (233932738253507701538139474372509264945857839023) }

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
  base := (15028391542677778943214203677170514887627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-68458787177041133036532841613565321000000000000)
      constant := (233881541104494885268905046313342816662718055587) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel008
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
  base := (10419170658523852982415042084912265887977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-78090020659100546731389880547017596000000000000)
      constant := (238167366858323511638225058047902028094733573937) }

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
  base := (10383598434545314951517545942701449584453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-78177059053046228478214308172822596000000000000)
      constant := (238272710422601864624133016596802303838274294893) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel009
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
  base := (3458314247509381335559563768570881013613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (57832177310575205112230800257100000000000000)
      linear := (-541959337875694024411841318845983000000000000)
      constant := (1578854218592924579377626828539338270998015813) }

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
  base := (3443845797842399533463486690475498526331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (57832177310575205112230800257100000000000000)
      linear := (-542563771166983480987010955136295500000000000)
      constant := (1580394449402974471064665720406448215627517731) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel010
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
  base := (832643815629322873311586206540727536137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-97504804812624317178046706759080896000000000000)
      constant := (283835334188136111670680653631391793395564494485) }

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
  base := (4138872466917395599148935348099247088807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-97613602805056419361577241291337146000000000000)
      constant := (284225495614413970080550905230710090782901203167) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel011
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
  base := (385994409547364079684908764958385339867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-107212196889386202401375119865112546000000000000)
      constant := (320692134673832033699378636413229794021627115135) }

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
  base := (11931002161935868586861213810804323917/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-26832968670265378700814676962648605250000000000)
      constant := (80306282158871114864028664667219853527949543080) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel012
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
  base := (40678396764357149575268563625600352731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-6495532720341560423594640720619122000000000000)
      constant := (20297963473890029259613088961893844674210537179) }

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
  base := (503283777229994611592917720352024179/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-13005571839674067804993352712205744000000000000)
      constant := (40671652866569391305809170990665330727830126375) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel013
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
  base := (-1467033038543698515718103411465996017507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (55436761682326527977404672435800000000000000)
      linear := (-749272077176982087858177195722934000000000000)
      constant := (2468862312115108982616715432150957411645842557) }

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
  base := (-185424387405928986779308881853288914627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13859190420581631994351168108950000000000000)
      linear := (-187527246202768795394410711492764750000000000)
      constant := (618455027523083592917204017599879182531795354) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel014
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
  base := (-554171353142848473094349849122610372339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-136334373119671858071360359183207496000000000000)
      constant := (475912243437908996501467398202579308091521029705) }

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
  base := (-111417959257136337408039291145225426753/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-136486690309076801128303107528366246000000000000)
      constant := (476915448351269837158579752642928436661281470175) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel015
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
  base := (-967248156233331486721943919644766901893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-4056715699900937313741354785812198500000000000)
      constant := (15030704016311038318633748536998064216584775163) }

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
  base := (-3882034815396394287800010514402120696039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-16244995798342432952220508231958169000000000000)
      constant := (60253730448517327312293313058551205162630756249) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel016
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
  base := (-2395022013265621319928856755605570991163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-77874578636597814259008592697635398000000000000)
      constant := (306304951571438271867678626533157882173341967597) }

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
  base := (-1200425680023900494480456967698812362323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-38980808515271748002916510161720199000000000000)
      constant := (153493307629470144925503424247491045555672879637) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel017
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
  base := (-5555964297043879605603950897103407324471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-165456549349957513741345598501302446000000000000)
      constant := (690266944507950066598958454816858674699582418449) }

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
  base := (-695796954425975988066919926107286636301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-41410376484273021863336876801534517750000000000)
      constant := (172956415810581428198329875152983387059282296438) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel018
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
  base := (-3092072886491049097369558831914120025303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (57832177310575205112230800257100000000000000)
      linear := (-1081258897695798759041197602514408000000000000)
      constant := (4777472360543388514182239847698521005617886497) }

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
  base := (-6193427780978699586205927541728193876163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-2164935528556755344383073750190066000000000000)
      constant := (9576729100352312002307769121966217614277151637) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel019
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
  base := (-668867844433402810957067469154317242547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-92435666751740642094001212356682873000000000000)
      constant := (431779302224161965183127660237658451038117539465) }

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
  base := (-3348468672902445425690296409980831716791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-92539024844551139168355220162326310500000000000)
      constant := (432769732619190934889903221654624225555535592529) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel020
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
  base := (-7081149730944496192091571602925366321913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-194578725580243169411330837819397396000000000000)
      constant := (959007280548189703280573903434754335361827126847) }

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
  base := (-1417696609577907259447027233066039443377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-194796321565107373778391906883909896000000000000)
      constant := (961215040505435303616439862696717250627674393315) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel021
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
  base := (-7371182852542529723971596434736036417531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-22698457517445006070517694547269894000000000000)
      constant := (117802984927199964647976131762582118349126799621) }

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
  base := (-922210105471559126547150814758585455301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-5680960928919790811668704817865754750000000000)
      constant := (29518670810086597713238387521841359591728935382) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel022
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
  base := (-945852509271613294883358130850954430233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-53498377433441734964496916007865174000000000000)
      constant := (291789779482158786122566382006998930448203809854) }

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
  base := (-3786283186180643052839826237937771823763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-107116432658558782330877420001212223000000000000)
      constant := (584926300642478186819223521520926888093384886997) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel023
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
  base := (-7674809128540987116129561101167388888137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (985608)
      previous := (492804)
      next := (492804)
      square := (17710421028947416310361795163800000000000000)
      linear := (-422875050681528969907969900070874000000000000)
      constant := (2419196933310996485520945837867568488510292607) }

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
  base := (-959985129108325393528685820893639488199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34222500000000000000000000000000000000000000
      center := (246402)
      previous := (123201)
      next := (123201)
      square := (4427605257236854077590448790950000000000000)
      linear := (-105837021357808440502569142987562250000000000)
      constant := (606194508108059875684278066584240649029587778) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel024
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
  base := (-7700825681442948990485790755117757583069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-25934254876365634478293832249280444000000000000)
      constant := (155330438166380033922048728881443812188844434979) }

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
  base := (-3852647168575762599802520905339169696711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-12981633837173764196950987395607722000000000000)
      constant := (77844223728654253704501201209458584009499059001) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel025
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
  base := (-3824825535673271596634767346463649443813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-121557842982026297763986451674777823000000000000)
      constant := (760890395642337924177843226775824851299467592947) }

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
  base := (-382679082198818210113144348492185968969/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-60846920236283212746699809920049067750000000000)
      constant := (381320841123147750088085601412661061997159484555) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel026
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
  base := (-1881329280493971127374345658770168173983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13859190420581631994351168108950000000000000)
      linear := (-373998636155051007028552243277496000000000000)
      constant := (2442524444834896809992318505831693688913002433) }

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
  base := (-7528769008691992267054395961312383815191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (55436761682326527977404672435800000000000000)
      linear := (-1497668359888390215553140273606234000000000000)
      constant := (9792546962625856267678903091668531540902880841) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel027
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
  base := (-7331225676199762204027642885213653470081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-3241116915031806987341107772365666000000000000)
      constant := (22049956906025483554831181751009868041121288519) }

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
  base := (-7334252763902099023764106809066749404709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-3244743514779543726792125590107541000000000000)
      constant := (22100526533472757954977981556787914130219610691) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel028
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
  base := (-7070248102099546521824392680759939799629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-272237862194338251197958142667650596000000000000)
      constant := (1926459952366292372432368978222964218379842789451) }

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
  base := (-7072899066896446594516916937213059453087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-272542496573148137311843639357968096000000000000)
      constant := (1930869246851605231796900932150547587518600098153) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel029
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
  base := (-6744808574991530314490732144247921473393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-281945254271100136421286555773682246000000000000)
      constant := (2072369299023581253352617410037332648235932584967) }

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
  base := (-6747127211886255451624386971198930860747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-282260768449153232753525105917225371000000000000)
      constant := (2077102710331641258531732708294634425045336953693) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel030
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
  base := (-6356954018379132147939171029308279229787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-32405849594206891293846107653301544000000000000)
      constant := (247084414066919150191329814470185927257200311717) }

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
  base := (-6358979588955609544135110411537196742997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-32442115591684258688356285830720294000000000000)
      constant := (247647583302490332470919052957932709540813926827) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel031
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
  base := (-1181682593290910290450743865538887460497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-301360038424623906867943381985745546000000000000)
      constant := (2380618717954855005019257552046893731343363619715) }

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
  base := (-236407222137820298822982385917880896303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-301697312201163423636888039035739921000000000000)
      constant := (2386033378137481343044268400804651539072721381425) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel032
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
  base := (-1080129033802004424494385671905827872073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-311067430501385792091271795091777196000000000000)
      constant := (2542935702330943997546014653311800040375564699435) }

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
  base := (-5402186028556251307801765152367687533879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-311415584077168519078569505594997196000000000000)
      constant := (2548707552536653864265888272003436557709478365201) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel033
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
  base := (-2417441714734751123137427053986391643717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-17820823476563759850811122677656047000000000000)
      constant := (150594541800442666770305607392466662843440508347) }

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
  base := (-2418112666981444630313003784193373742411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-17840769775176311917791720675236359500000000000)
      constant := (150935659490270042675217809767419021543367427701) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel034
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
  base := (-4212168910376462270081330945893292026823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-330482214654909562537928621303840496000000000000)
      constant := (2883909328627150565065912884151423424260309755137) }

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
  base := (-4213336476709202672798037179431532679019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-330852127829178709961932438713511746000000000000)
      constant := (2890428816293816645939439785321785401179004812861) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel035
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
  base := (-706676187179613786602668907303767218781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-340189606731671447761257034409872146000000000000)
      constant := (3062552063379242308382066690710331324158872726695) }

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
  base := (-44179949194910323586424312941026762827/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-85142599926295951350903476318192255250000000000)
      constant := (767365510484740381421397204129228241178372964260) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel036
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
  base := (-2799262154111063341198523578121011452939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-4319716034672016456599820339702516000000000000)
      constant := (40081784923361800303111359826512779455095800461) }

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
  base := (-700035950788460167190563136590859912601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 223502500000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (28916088655287602556115400128550000000000000)
      linear := (-1081137875250583027300294357506254000000000000)
      constant := (10043012927142679517120258153047037657953557999) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel037
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
  base := (-1005219892093501112035342745477235351259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-179802195442597609103956930310967723000000000000)
      constant := (1718061166435313724889578060128395888708829625421) }

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
  base := (-1005602505721955054080837984513488276593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-180003471728596998143488419195641785500000000000)
      constant := (1721923365113019075120120366659003123198204045767) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel038
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
  base := (-9339548472240985150921641747602542413/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-369311782961957103431242273727967096000000000000)
      constant := (3631041489563446072937060828457368834695570793375) }

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
  base := (-146013406617145390606288223165963958043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-92431303833299772932164576237635211500000000000)
      constant := (909797461539841559550396546126782316771043636634) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel039
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
  base := (-2165767024389431589035279650100107971/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (342792)
      previous := (171396)
      next := (171396)
      square := (6159640186925169775267185826200000000000000)
      linear := (-249190779118158440930026750055226000000000000)
      constant := (2518986725204764904525577688074395048243758625) }

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
  base := (-135648055930672061392273269208785154947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (3079820093462584887633592913100000000000000)
      linear := (-124734874164761402751590983402300500000000000)
      constant := (1262315026135599380886552717563136395752297333) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel040
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
  base := (339675197883088797950980779353207483909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-194363283557740436938949549970015198000000000000)
      constant := (2018565777500980227198509531982453114283784829229) }

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
  base := (678852159449732273116340320702932136357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-389161759085209282612021238069055396000000000000)
      constant := (4046161395637292861342287321946348529709718624717) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel041
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
  base := (13144149437734671857172309014289643583/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-99608489798060689775306878261515511500000000000)
      constant := (1062074354113601008996692945070090831808848125536) }

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
  base := (84100992623353549048160497926064332141/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-99720007740303594513425676157078167750000000000)
      constant := (1064446200969372154105793590861715777790821204105) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel042
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
  base := (1369155892545801254827254709139407697663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-22674519514944702462475329230671872000000000000)
      constant := (248048580087275745378237015376895254938208928767) }

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
  base := (547587738624618973124669940555549565853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-45399811426357719277264907909729994000000000000)
      constant := (497203399058168603262161835559330720778157082385) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel043
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
  base := (3846704724915359842218353588768737526081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-417848743345766529547884339258125346000000000000)
      constant := (4686860981886163640533353714750039626064102565961) }

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
  base := (1923191074964283188788354288023331674661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-209158287356612284468532818873413610500000000000)
      constant := (2348648559075952042365898891717814683425630812941) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel044
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
  base := (2503718843086205006721982548858156395737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-213778067711264207385606376182078498000000000000)
      constant := (2457127822571622221595864846402612973234757966497) }

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
  base := (5007158938957446095827032943266022048523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-428034846589229664378747104306084496000000000000)
      constant := (4925182998583732562667802781882339263109960382563) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel045
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
  base := (6220348289289755346202829309209430322723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-5398315154312225925858532907039366000000000000)
      constant := (63543916734242137950511406637722149155281758923) }

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
  base := (3110053769725258162013031897105918498717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (57832177310575205112230800257100000000000000)
      linear := (-2702179743612560245805114634971245500000000000)
      constant := (31842512735614159769410505113385743016578798517) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel046
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
  base := (7485299392166372808582081420640120109147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (985608)
      previous := (492804)
      next := (492804)
      square := (17710421028947416310361795163800000000000000)
      linear := (-844935575758132675270074817724424000000000000)
      constant := (10180084725454349668367253393529659104174113283) }

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
  base := (935636445347329394751456202696143542807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34222500000000000000000000000000000000000000
      center := (246402)
      previous := (123201)
      next := (123201)
      square := (4427605257236854077590448790950000000000000)
      linear := (-211470411314385564868672040370793500000000000)
      constant := (2550665559666125471416162987634565236664970046) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel047
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
  base := (1760435033543306450952500722537692940367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-456678311652814070441197991682251946000000000000)
      constant := (5628877499258817244694211920096846084932508817635) }

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
  base := (8801995841980799901872734129027441649257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-457189662217244950703791503983856321000000000000)
      constant := (5641345947856455478520711250421425319025453229617) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel048
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
  base := (2034175558209977025177776454047248888857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-51820633747730661740502933865364844000000000000)
      constant := (653099398395214133133655683474404826406071709565) }

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
  base := (10170723129755791535887876111426109429477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-51878659343694449571719218949234844000000000000)
      constant := (654544358862645749649853499149862062481942059493) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel049
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
  base := (1448915580192022893470209487741193852471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-119023273951584460221963704473578811500000000000)
      constant := (1533078870090989171047361492194307682868721099102) }

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
  base := (5795595655116612142743785441294600875991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-238313102984627570793577218551185435500000000000)
      constant := (3072933787667537552725648128126192833317947182671) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel050
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
  base := (13063445939729787505567024198579427222379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-485800487883099726111183231000346896000000000000)
      constant := (6392139678373375918643509284653962011721740303299) }

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
  base := (13063331044581471871635159617682065282551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-486344477845260237028835903661628146000000000000)
      constant := (6406250482454413770429810878948784161659352698031) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel051
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
  base := (3646795687891775940778070776182872628267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-13764107776662822537069767891843848500000000000)
      constant := (184926854244868975823991565406458372681307282603) }

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
  base := (14587083782949034333925293848270904951741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-55118083302362814718946374468987269000000000000)
      constant := (741338614126021172444383253022823513406065374269) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel052
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
  base := (4040621325688680809062430550111793962257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13859190420581631994351168108950000000000000)
      linear := (-747359869876661977156568131971021000000000000)
      constant := (10248515300665796316329166253970032259488750193) }

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
  base := (505075002679354333234208749392647935817/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13859190420581631994351168108950000000000000)
      linear := (-748196777510755070876033782219146000000000000)
      constant := (10271092235737435235283158400688474696214581064) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel053
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
  base := (17789311555137946177671494607933568339787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-514922664113385381781168470318441846000000000000)
      constant := (7204028145259262925887134809491236469269769104547) }

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
  base := (1111827387880500509363694400500866160033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-128874823368318880838470075834849992750000000000)
      constant := (1804970663204558894514901183626472725274125215492) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel054
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
  base := (19467626004332321520563910293512983286453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-6476914273952435395117245474376216000000000000)
      constant := (92413109898006315539676426581928630718792184653) }

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
  base := (1946756289290064227119866977823591036027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (57832177310575205112230800257100000000000000)
      linear := (-3242083736723954437009640554929983000000000000)
      constant := (46308149236069433940986038391364027248559249135) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel055
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
  base := (21197398664229204706557005833743608709443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-534337448266909152227825296530505146000000000000)
      constant := (7772297395543988194813294137517140828215866005083) }

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
  base := (10598672190066437068433140162794522743059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-267467918612642857118621618228957260500000000000)
      constant := (3894685353041649826097648332242617784519804630379) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel056
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
  base := (5744651052332781408186209987516197064333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-136011210085917759362788427409134199000000000000)
      constant := (2016133610820396022221846036019547247233623197173) }

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
  base := (2297855753333424184966380968127921775003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-272327054550645404839462351508585898000000000000)
      constant := (4041117030163872087028392750107286643515852497215) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel057
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
  base := (24811221250386848791806026465335328493497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-61528025824492546963831346971396494000000000000)
      constant := (929130321117938090531474154880436998198824127673) }

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
  base := (24811181128986329615321752053180170444387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-61596931219699545013400685508492119000000000000)
      constant := (931167787254097389211100243501768147854837779683) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel058
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
  base := (26695231722608509370531345844205376351031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-563459624497194807897810535848600096000000000000)
      constant := (8665212605067746280425520774764308023443840316911) }

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
  base := (26695197245972983904613657584975521202491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-564090652853301000562287636135686346000000000000)
      constant := (8684198651185274514149670457057287887127935729171) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel059
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
  base := (28630620368973165938352826304691745320763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-573167016573956693121138948954631746000000000000)
      constant := (8973653477817052738880573499731546720472144170003) }

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
  base := (28630590751735352273726643788414899138219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-573808924729306096003969102694943621000000000000)
      constant := (8993299648440800796452415740744799172320079262339) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel060
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
  base := (30617374303830617299048408785312968591119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-64763823183413175371607484673407044000000000000)
      constant := (1031943934999796787282200695150117022345131667471) }

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
  base := (7654337217094801055756833378933901106739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-16209088794591977540156960257061136000000000000)
      constant := (258550360681182696100983956527696927860592160051) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel061
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
  base := (3265548264433616901415465609017440015903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-296290900363740231783897887583347523000000000000)
      constant := (4803369168901594119838140197487031554156506361715) }

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
  base := (32655460806294308656909252227804474184597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-593245468481316286887332035813458171000000000000)
      constant := (9627738581297845817814247070962042023616499668157) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel062
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
  base := (3474493619916689591085308539733923198029/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-301144596402121174395562094136363348000000000000)
      constant := (4965691089836656936893304577898347331719931204745) }

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
  base := (34744917454781284199425254373878527639587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-602963740357321382329013502372715446000000000000)
      constant := (9953076372791650604043214537129717203085044108347) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel063
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
  base := (3688572720561831241046771256401667234701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (3218436)
      previous := (1609218)
      next := (1609218)
      square := (57832177310575205112230800257100000000000000)
      linear := (-3777756696796322432187979020856533000000000000)
      constant := (63342141261697968808259483916621154699747520505) }

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
  base := (36885711120815803603047503184675259975123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-7563975459670697256428332949777441000000000000)
      constant := (126960818559198789136068761809435238260785971323) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel064
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
  base := (19538924553781045749781190481031084185861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-310851988478883059618890507242394998000000000000)
      constant := (5298436202246190372750488719063063728541312900141) }

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
  base := (244236470677876146567700696612264302729/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-155600071027332893303094108872807499000000000000)
      constant := (2654997081441997613525374585506136088607612065960) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel065
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
  base := (8264259273582828299134892958234894102427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (55436761682326527977404672435800000000000000)
      linear := (-3736161946949869848882304305271134000000000000)
      constant := (64720228993305053397364622181977541761974472615) }

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
  base := (20660642266298897752196089897951840327907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (27718380841163263988702336217900000000000000)
      linear := (-1870173242560167658739816278255879500000000000)
      constant := (32430657989615231834646917872403097703085487043) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel066
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
  base := (681501004847646599692973193684154767589/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-17808854475313608046789940019357036000000000000)
      constant := (313443492684981872722829320993638291959320283216) }

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
  base := (21808027080824904827368693251392042495963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-35657601547852320227541076033874697000000000000)
      constant := (628252694106749196656253781075775100358134293467) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel067
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
  base := (22981074492516595193475574762056640680991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-325413076594025887453883126901442473000000000000)
      constant := (5817806743132140495127209074926638061352723387671) }

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
  base := (45962140284764734806721410574190036099793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-651555099737346859537420835169001821000000000000)
      constant := (11660946577742245226620056521726297677399715113433) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel068
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
  base := (9671909411328708641465096385234831179171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-660533545264813660131094666908916596000000000000)
      constant := (11992661924528511243126253131983836280610871961255) }

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
  base := (24179769799836443737379131700795882373109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-330636685806675977489551150864129548000000000000)
      constant := (6009378314019452125348119458792199937333103734429) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel069
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
  base := (6351031963494066933534913609553632952701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3802500000000000000000000000000000000000000
      center := (27378)
      previous := (13689)
      next := (13689)
      square := (491956139692983786398938754550000000000000)
      linear := (-35194336134298232795338325982721500000000000)
      constant := (648766594783231462681557363965351120192116442) }

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
  base := (10161649863598081149136604137967952048171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (109512)
      previous := (54756)
      next := (54756)
      square := (1967824558771935145595755018200000000000000)
      linear := (-140935022787094528548788861224011000000000000)
      constant := (2600709646002821645723652131440557619076340455) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel070
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
  base := (53308272559738152186419251654121268408423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-679948329418337430577751493120979896000000000000)
      constant := (12722960788605236170514435604438043269375495394463) }

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
  base := (26654133542628862884699016161517461710749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-340354957682681072931232617423386823000000000000)
      constant := (6375306275217029921756747090439825701084116379269) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel071
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
  base := (55859595602621350630346663830422823369917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-689655721495099315801079906227011546000000000000)
      constant := (13096211182637759669009213225689450460274609927077) }

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
  base := (218201527005546457577787164950622699657/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-172607046810341810326036675351507730250000000000)
      constant := (3281164597771580009019739189823303774770969309088) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel072
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
  base := (11692444627916347968978451580784974603579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-8634112513232854333634670609049916000000000000)
      constant := (166356323467413451272561494517103439572672830895) }

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
  base := (1461555478095320115795918424399396094383/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 223502500000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (28916088655287602556115400128550000000000000)
      linear := (-2160945861473371409709346197423729000000000000)
      constant := (41679370785247531555857948658477167102339345830) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel073
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
  base := (61116153737407707985470117435764060326627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-709070505648623086247736732439074846000000000000)
      constant := (13858913832894851166567295228266211043213123214587) }

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
  base := (61116150299020694363732472246235507675883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-709864730993377432187509634524545471000000000000)
      constant := (13888985770171511069839688540410689998204010902723) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel074
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
  base := (31910693092846192048426557922309533807547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-359388948862692485735532572772553248000000000000)
      constant := (7124183034987853075593463327504357248436209257107) }

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
  base := (15955345810556132202022874316749739810607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-179895750717345631907297775270950686500000000000)
      constant := (3569816822418377570394068817615876260312204188967) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel075
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
  base := (13315583892440528327125663509917481548011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-80942809978016317410488173183459794000000000000)
      constant := (1627024322744508082611294987549951071429317913495) }

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
  base := (66577916942875749639087798327885810031701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-81033474971709735896763618627006669000000000000)
      constant := (1630551187289814408290430518657287576067546909909) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel076
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
  base := (2168304771988457142423516160752789254827/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-184548170469727185479430492939292449000000000000)
      constant := (3760868082704455883945570398939475351686671030296) }

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
  base := (34692875273855580005074529788117860726567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-369509773310696359256277017101158648000000000000)
      constant := (7538032975898540010494386696196950393462081125727) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel077
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
  base := (36122442590445628242200865874491207948569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-373950036977835313570525192431600723000000000000)
      constant := (7724563171523901356577288496335053136464111390689) }

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
  base := (72244883336277888164790866251314198780099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-748737818497397813954235500761574571000000000000)
      constant := (15482583083022615538480952927612464458590060086619) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel078
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
  base := (37577658139129551192714004747665784225037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (3079820093462584887633592913100000000000000)
      linear := (-249049134132949543841018671258788000000000000)
      constant := (5213734693271448495570156926179607048695401157) }

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
  base := (751553147002666729418232841106547252849/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11902500000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (1539910046731292443816796456550000000000000)
      linear := (-124664051672156954207086944004081500000000000)
      constant := (2612510202971708788669891260250363005520352225) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel079
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
  base := (19529261368936997271101390341599518416997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-191828714527298599396926802768816186500000000000)
      constant := (4069159027176046086151882505796988742444583852557) }

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
  base := (4882315257878806638348294415130511056279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-192043590562352001209399608470022280250000000000)
      constant := (4077963230912379326826943981213177001798274736796) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel080
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
  base := (20282518083557314123490155141669771503663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-194255562546489070702758906045324099000000000000)
      constant := (4174622963796293731956434870442703128618117044903) }

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
  base := (8113007118000106820148572762986030188687/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-388946317062706550139639950219673198000000000000)
      constant := (8367302813095600738327953317293262294384016627235) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel081
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
  base := (10524299560357883300458408159138196861081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 223502500000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (28916088655287602556115400128550000000000000)
      linear := (-2428177908218265950723345794096691500000000000)
      constant := (52857247449658297625725840834560794843905004962) }

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
  base := (21048598873985511611955439758683085407291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 223502500000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (28916088655287602556115400128550000000000000)
      linear := (-2430897858029068505311609157403097750000000000)
      constant := (52971512900782394762982774297060047979434722691) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel082
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
  base := (8731001760848324025345617574329889144939/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-398218517169740026628846225196679848000000000000)
      constant := (8779202530974368960725239765735625067125910073295) }

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
  base := (87310016764746570169267821845812234868623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-797329177877423291162642833557860946000000000000)
      constant := (17596346582397788914190096554308803222243670950663) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel083
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
  base := (18095387089326400751655584278526717158663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-806144426416241938481020863499391346000000000000)
      constant := (17996462518048457452184186749352086241359160499515) }

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
  base := (90476934725413503644962573709791389540951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-807047449753428386604324300117118221000000000000)
      constant := (18035334831934045744305900966484588162918145388431) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel084
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
  base := (93695149773988202582743245648451933742947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-90650202054778202633816586289491444000000000000)
      constant := (2048880060041252347435389461662797757956978842723) }

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
  base := (46847574578793308393917651501885103181547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-45375873423857415669222542593131972000000000000)
      constant := (1026651940381475607785926733605616875235801350123) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel085
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
  base := (96964660401972409190904900544996704548033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-825559210569765708927677689711454646000000000000)
      constant := (18888779127551584604160995935164211237922194556873) }

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
  base := (96964659875229032060503932974990531043741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-826483993505438577487687233235632771000000000000)
      constant := (18929546865848151987726158171012710124326910620421) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel086
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
  base := (100285467171346002440455794550268309123737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-835266602646527594151006102817486296000000000000)
      constant := (19343038278436274434443443990454944573921668134497) }

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
  base := (20057093344256393851909779145321241601723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-836202265381443672929368699794890046000000000000)
      constant := (19384770647741480714318092928866185877651433358815) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel087
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
  base := (12957196243456216401001238711602095186837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-23471499853424707760398180997875498500000000000)
      constant := (550074944223657125152267244889762950381121463466) }

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
  base := (12957196195394328958008961740617600372491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2011522500000000000000000000000000000000000000
      center := (14482962)
      previous := (7241481)
      next := (7241481)
      square := (260244797897588423005038601156950000000000000)
      linear := (-23497792701595799121418060176504092250000000000)
      constant := (551261285321844260685923241863643401534656722038) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel088
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
  base := (107080968617351284445729913512369460637117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-854681386800051364597662929029549596000000000000)
      constant := (20267758267575588743936522277792028862183930650277) }

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
  base := (53540484144457953892277408504237100861057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-427819404566726931906365816456702298000000000000)
      constant := (10155726868286171490845683376894546309380427905417) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel089
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
  base := (110555663084591669325682484378316260213683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-864388778876813249820991342135581246000000000000)
      constant := (20738219104313910074565532957881680126203441384523) }

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
  base := (110555662804078685713254397838383039640369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-865357081009458959254413099472661871000000000000)
      constant := (20782913042015102879687682102207662611121728946489) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel090
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
  base := (114081653268437326538238007301061073467867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (6436872)
      previous := (3218436)
      next := (3218436)
      square := (115664354621150410224461600514200000000000000)
      linear := (-10791310752513273272152095743723616000000000000)
      constant := (261902228415809156362538233115011663529100777667) }

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
  base := (356505165715264277540730508865673946611/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 223502500000000000000000000000000000000000000
      center := (1609218)
      previous := (804609)
      next := (804609)
      square := (28916088655287602556115400128550000000000000)
      linear := (-2700849854584765600913872117382466500000000000)
      constant := (65616617862151556064333005050096006038827600880) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel091
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
  base := (14707367387569922154968580692653539673889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 107122500000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (13859190420581631994351168108950000000000000)
      linear := (-1307401720459078432348591965011308500000000000)
      constant := (32093701862693315441478012234697533261722939522) }

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
  base := (117658938896011129362915726329231413901081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (3085128)
      previous := (1542564)
      next := (1542564)
      square := (55436761682326527977404672435800000000000000)
      linear := (-5235465235274965385430627411782109000000000000)
      constant := (128651285041720903881329418724020233197997419769) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel092
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
  base := (121287520523273613322283406165288572383497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (985608)
      previous := (492804)
      next := (492804)
      square := (17710421028947416310361795163800000000000000)
      linear := (-1689056625911340085994284653031524000000000000)
      constant := (41931956477120245173483030034520143267357690433) }

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
  base := (1895117505447436752790877236365938839077/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 34222500000000000000000000000000000000000000
      center := (246402)
      previous := (123201)
      next := (123201)
      square := (4427605257236854077590448790950000000000000)
      linear := (-422737191227539813600877835137256000000000000)
      constant := (10505558599123256244356763398211381013290000848) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel093
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
  base := (24993479497577032206314418470451447367387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-100357594131540087857144999395523094000000000000)
      constant := (2519340894775078226364090048443043806949129433415) }

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
  base := (12496739733880195051002414252311977856011/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-50235009361859963390063275872760609500000000000)
      constant := (1262381592115097566870574043159439500625610773495) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel094
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
  base := (12869856995329046260723350589853383554819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (260693316)
      previous := (130346658)
      next := (130346658)
      square := (4684406362156591614090694820825100000000000000)
      linear := (-456462869630311337968816703832869748000000000000)
      constant := (11585765844310156813698897957142820467239671234695) }

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
  base := (128698569826037075001623229068780348614687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-913948440389484436462820432268948246000000000000)
      constant := (23221387158738593151339901096153284908541632231447) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel095
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
  base := (132481037884796580812770256083533043927437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-922633131337384561160961820771771146000000000000)
      constant := (23674395883079210221303190961703200867347700414197) }

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
  base := (132481037776188830864013553399169689327971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-923666712265489531904501898828205521000000000000)
      constant := (23725317497498006413947578297884213555888154765051) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel096
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
  base := (136314801253124047473678055077786068564437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (57931848)
      previous := (28965924)
      next := (28965924)
      square := (1040979191590353692020154404627800000000000000)
      linear := (-103593391490460716264921137097533644000000000000)
      constant := (2686962292904485234057468677056049394841563090133) }

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
  base := (68157400580220088892602120208460677737037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (28965924)
      previous := (14482962)
      next := (14482962)
      square := (520489595795176846010077202313900000000000000)
      linear := (-51854721341194145963676853632636822000000000000)
      constant := (1346369981896739885644324910437319149453319603533) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel097
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
  base := (8762491252097795452763582567242304853247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-235511978872727082901904661745958611500000000000)
      constant := (6174081486906215197597068924274376525432733755228) }

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
  base := (140199859954478588108072330213371421134549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-943103256017499722787864831946720071000000000000)
      constant := (24749413688492469027199680937273526756432585027069) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell107.Kernel098
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
  base := (144136214205270601937796284123628706051733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (521386632)
      previous := (260693316)
      next := (260693316)
      square := (9368812724313183228181389641650200000000000000)
      linear := (-951755307567670216830947060089866096000000000000)
      constant := (25215391817381720745330505015602843596428209536573) }

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
  base := (36034053534448607634041165210124627208541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18103702500000000000000000000000000000000000000
      center := (130346658)
      previous := (65173329)
      next := (65173329)
      square := (2342203181078295807045347410412550000000000000)
      linear := (-238205381973376204557386574626494336500000000000)
      constant := (6317394885100734891350701251613259990531482689221) }

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
end ForestUnimodality.Stage80KernelData.Cell107.Kernel098
