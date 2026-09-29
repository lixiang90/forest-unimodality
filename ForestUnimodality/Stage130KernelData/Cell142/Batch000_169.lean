import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell142.Parameters
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch000_049
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch050_099
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch100_149
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch150_199
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree000.table
  base := (169830332811514122917628813/2500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (182814824601663754310987287500000000000)
      linear := (-13122636123498400331083280000000000000)
      constant := (169830332811514122917628813000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree000.table
  base := (169830332811514122917628813/2500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (182814824601663754310987287500000000000)
      linear := (-13122636123498400331083280000000000000)
      constant := (169830332811514122917628813000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree001.table
  base := (380656122754678709067760741108108716665449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-103140711243071051258205937780094067500000000000)
      constant := (47633623587681028329597825830307861310595585895561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree001.table
  base := (380577435628271530224488197292523676872907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-103166266470365056330261684915545473750000000000)
      constant := (47623797428570810462659256617984163684619054864523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12480156559969647623/25000000000000000000)
  directionHi := (49920626239878590493/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree002.table
  base := (227346362826062689668028828828963292940751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-199716981814391499165521052307212455000000000000)
      constant := (28540741182050290616008846261300766246802627336239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree002.table
  base := (22726590660601523147543042914880200550469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-99884046134489754654816273289057633750000000000)
      constant := (14265367592370178062845907676855969974280234251705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/25000000000000000000)
  centralHi := (49920626239878590493/100000000000000000000)
  directionLo := (7059842667059450639/10000000000000000000)
  directionHi := (70598426670594506391/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree003.table
  base := (72782281526529342638963281227964867889581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-148146626192855973536418083417165421250000000000)
      constant := (9222051680593886758568029616556064364082883284109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree003.table
  base := (145500633370913846591217381583815690033063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-296369918067593962289003408240685061250000000000)
      constant := (18436232559047597152585224982576261996146939384807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7059842667059450639/10000000000000000000)
  centralHi := (70598426670594506391/100000000000000000000)
  directionLo := (8646506099312579899/10000000000000000000)
  directionHi := (86465060993125798991/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree004.table
  base := (9962431664258830777124628998637705530093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-196434761478516197490075640680724615000000000000)
      constant := (6440393163652482538486134139201545252379523512385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree004.table
  base := (6223560818171606671401869933500982075533/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-98242935966552103817093567475813713750000000000)
      constant := (3218771290991844726201275057980533195426015530548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646506099312579899/10000000000000000000)
  centralHi := (86465060993125798991/100000000000000000000)
  directionLo := (12480156559969647623/12500000000000000000)
  directionHi := (19968250495951436197/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree005.table
  base := (14427571562894105527522366340826822322453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-489445793528352842887466395888567617500000000000)
      constant := (9676284977080739417455908164097123784917577032585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree005.table
  base := (14420608705124036871063065802636262774611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-489573569664822868247745131565824648750000000000)
      constant := (9672273093830804082088617102626354139617556668895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/12500000000000000000)
  centralHi := (19968250495951436197/20000000000000000000)
  directionLo := (69766196094830157/62500000000000000)
  directionHi := (111625913751728251201/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree006.table
  base := (54525552645332760587141520335817648537639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-586022064099673290794781510415686005000000000000)
      constant := (7757634676251055990684949710516895250173730606471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree006.table
  base := (54499394167147294575593957866426535483187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-586175395463437321227115993228394442500000000000)
      constant := (7754854652157830965841822608744416225286484311443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69766196094830157/62500000000000000)
  centralHi := (111625913751728251201/100000000000000000000)
  directionLo := (24456012385579075971/20000000000000000000)
  directionHi := (7642503870493461241/6250000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree007.table
  base := (4247109607717662478127570703953704929319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-341299167335496869351048312471402196250000000000)
      constant := (3292520259947260900551121368738061285821451289955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree007.table
  base := (42450806669064733019366830152987990598341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-682777221262051774206486854890964236250000000000)
      constant := (6583170837641470709851851066286729957482517207749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24456012385579075971/20000000000000000000)
  centralHi := (7642503870493461241/6250000000000000000)
  directionLo := (66038781161662092001/50000000000000000000)
  directionHi := (132077562323324184003/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree008.table
  base := (2108728335524458215856923411663682650669/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-194793651310578546652352934867480695000000000000)
      constant := (1469753804306461142176729113876328816103322592564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree008.table
  base := (33723426289774396606629065771540918576703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-779379047060666227185857716553534030000000000000)
      constant := (5877856917797237499563966052275352547293084484767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66038781161662092001/50000000000000000000)
  centralHi := (132077562323324184003/100000000000000000000)
  directionLo := (141196853341189012781/100000000000000000000)
  directionHi := (70598426670594506391/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree009.table
  base := (5425342608935680512193500481542043324017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-875750875813634634516726853997041167500000000000)
      constant := (5488923178774619995903739758082891676055887236565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree009.table
  base := (27113421130790429627747453728626547311573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-875980872859280680165228578216103823750000000000)
      constant := (5488362290558590346203705822439147612486830666197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141196853341189012781/100000000000000000000)
  centralHi := (70598426670594506391/50000000000000000000)
  directionLo := (37440469679908942869/25000000000000000000)
  directionHi := (149761878719635771477/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree010.table
  base := (2743577952358953314168201204256801279119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-243081786596238770606010492131039888750000000000)
      constant := (1332316824725437900804729464151421284701087020382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree010.table
  base := (21937561652629869044372190151512371926443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-972582698657895133144599439878673617500000000000)
      constant := (5329242618848084567989156501203967059517657167627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37440469679908942869/25000000000000000000)
  centralHi := (149761878719635771477/100000000000000000000)
  directionLo := (39465720284995867381/25000000000000000000)
  directionHi := (6314515245599338781/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree011.table
  base := (1112080960954270687567517064948132855723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-267225854239068882582839270762819485625000000000)
      constant := (1337127962084826978914703062048650826818003922188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree011.table
  base := (8892002878719745181690290778061801846709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-534592262228254793061985150770621705625000000000)
      constant := (2674496570179753956404055013573894086146027621701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39465720284995867381/25000000000000000000)
  centralHi := (6314515245599338781/4000000000000000000)
  directionLo := (165567986537247602849/100000000000000000000)
  directionHi := (3311359730744952057/2000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree012.table
  base := (14396367784452481785135008982966166038019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1165479687527595978238672197578396330000000000000)
      constant := (5513596034366750222883016436462981176503810712291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree012.table
  base := (14388534786983066707562555366588571682671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1165786350255124039103341163203813205000000000000)
      constant := (5514570804709572206108608978279186054749705415119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165567986537247602849/100000000000000000000)
  centralHi := (3311359730744952057/2000000000000000000)
  directionLo := (8646506099312579899/5000000000000000000)
  directionHi := (172930121986251597981/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree013.table
  base := (11578281429080198329856263162811739940937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1262055958098916426145987312105514717500000000000)
      constant := (5802064248005915087825650639290060626933221401193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree013.table
  base := (1446458889923394401861918213433212514179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-315597044013434623020678006216595749687500000000)
      constant := (1450882558054962365223847186962199897598183864062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646506099312579899/5000000000000000000)
  centralHi := (172930121986251597981/100000000000000000000)
  directionLo := (1439931020889242751/800000000000000000)
  directionHi := (44997844402788835969/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree014.table
  base := (1842245120334468074277437245707135979677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1358632228670236874053302426632633105000000000000)
      constant := (6197932547490732750929452107793453388234600025265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree014.table
  base := (9205653178591540707824723653472395972659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1358990001852352945062082886528952792500000000000)
      constant := (6199893625474414533833473196671768516415142511251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1439931020889242751/800000000000000000)
  centralHi := (44997844402788835969/25000000000000000000)
  directionLo := (186785879922822774499/100000000000000000000)
  directionHi := (373571759845645549/200000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree015.table
  base := (900122755571758751253573035452088227683/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-363802124810389330490154385289937873125000000000)
      constant := (1672354511416104711520051599890572323716090767974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree015.table
  base := (7196294561724028442331006815245525323679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1455591827650967398041453748191522586250000000000)
      constant := (6691882081059322617927275039192040267258042840031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186785879922822774499/100000000000000000000)
  centralHi := (373571759845645549/200000000000000000)
  directionLo := (96670877029647381419/50000000000000000000)
  directionHi := (193341754059294762839/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree016.table
  base := (5476381035565492995025289552459641061997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1551784769812877769867932655686869880000000000000)
      constant := (7267620293433881452644434368471368884336762139533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree016.table
  base := (2736224162935179665728428958151498285963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-776096826724790925510412304927046190000000000000)
      constant := (3635298999324902150474151555406056375226908652907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96670877029647381419/50000000000000000000)
  centralHi := (193341754059294762839/100000000000000000000)
  directionLo := (12480156559969647623/6250000000000000000)
  directionHi := (199682504959514361969/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree017.table
  base := (995696830599380559010201163899219450407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-412090260096049554443811942553497066875000000000)
      constant := (1981426658517865909597039203548658507708947762023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree017.table
  base := (1989748548043688049916533651684528126549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-824397739624098152000097735758331086875000000000)
      constant := (3964605478622473464996125882979726530833439023461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/6250000000000000000)
  centralHi := (199682504959514361969/100000000000000000000)
  directionLo := (8233120595360000689/4000000000000000000)
  directionHi := (102914007442000008613/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree018.table
  base := (1338911162277228765648258236460583466727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-872468655477759332841281442370553327500000000000)
      constant := (4329188611976663289799871744401388267928227122503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree018.table
  base := (1337538648717312733884644832654016437453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-872698652523405378489783166589615983750000000000)
      constant := (4331211494905242106236336170894944057199847641517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8233120595360000689/4000000000000000000)
  centralHi := (102914007442000008613/50000000000000000000)
  directionLo := (211795280011783519171/100000000000000000000)
  directionHi := (52948820002945879793/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree019.table
  base := (764200247534765300163530790185877189769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-920756790763419556794938999634112521250000000000)
      constant := (4730747200741260367571393680141734094728642168041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree019.table
  base := (1526116462608255016837832011852781999789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1841999130845425209958937194841801761250000000000)
      constant := (9466098070485427157209583369491726851801697947821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211795280011783519171/100000000000000000000)
  centralHi := (52948820002945879793/25000000000000000000)
  directionLo := (217598964977895614863/100000000000000000000)
  directionHi := (13599935311118475929/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree020.table
  base := (101717523094255557796217128784596171731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1938089852098159561497193113795343430000000000000)
      constant := (10331814846549390499347047326965524729040175527295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree020.table
  base := (506691954884041589768802765053098784521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-1938600956644039662938308056504371555000000000000)
      constant := (10336994327567511782232845573241112988733717369769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217598964977895614863/100000000000000000000)
  centralHi := (13599935311118475929/6250000000000000000)
  directionLo := (69766196094830157/31250000000000000)
  directionHi := (223251827503456502401/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree021.table
  base := (-401995026076970725488277632616654462331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2034666122669480009404508228322461817500000000000)
      constant := (11266790007865163692718079713495914414270065391141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree021.table
  base := (-403564654332623025177844293815987766389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2035202782442654115917678918166941348750000000000)
      constant := (11272564495784963396427044972087919420959827784779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69766196094830157/31250000000000000)
  centralHi := (223251827503456502401/100000000000000000000)
  directionLo := (114382524241921187007/50000000000000000000)
  directionHi := (45753009696768474803/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree022.table
  base := (-1219384764049071204124186129400916164507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2131242393240800457311823342849580205000000000000)
      constant := (12264414264575617767390376588436284205209914643077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree022.table
  base := (-244136320855586893120764316017526615983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2131804608241268568897049779829511142500000000000)
      constant := (12270804091729333623049682225845625966025083936565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114382524241921187007/50000000000000000000)
  centralHi := (45753009696768474803/20000000000000000000)
  directionLo := (234148492055781574119/100000000000000000000)
  directionHi := (5853712301394539353/2500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree023.table
  base := (-489053486182504625455921461943049750351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-556954665953030226304784614344174648125000000000)
      constant := (3330776955477370054610721057812315224986713869361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree023.table
  base := (-489320812510118886112841824124558754341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-557101608509970755469105160373020234062500000000)
      constant := (3332533580001072436445004609590935076423434883251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234148492055781574119/100000000000000000000)
  centralHi := (5853712301394539353/2500000000000000000)
  directionLo := (935198878846569763/390625000000000000)
  directionHi := (239410912984721859329/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree024.table
  base := (-1311219186788788690660840731530015416009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1162197467191720676563226785951908490000000000000)
      constant := (7220812805961809786782884610387211418911792040599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree024.table
  base := (-1311659214105230882188070901655833138557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1162504129919248737427895751577325365000000000000)
      constant := (7224655492094857455728029291015053307572795382627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (935198878846569763/390625000000000000)
  centralHi := (239410912984721859329/100000000000000000000)
  directionLo := (24456012385579075971/10000000000000000000)
  directionHi := (244560123855790759711/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree025.table
  base := (-3225907055204146372226478124707212835729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2420971204954761801033768686430935367500000000000)
      constant := (15618986042112050629581865544866384668618240317519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree025.table
  base := (-3226630110686646047842186594381039605441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2421610085637111927835162364817220523750000000000)
      constant := (15627353246227709719857193006748657973271974420351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24456012385579075971/10000000000000000000)
  centralHi := (244560123855790759711/100000000000000000000)
  directionLo := (12480156559969647623/5000000000000000000)
  directionHi := (249603131199392952461/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree026.table
  base := (-943202320786541126729752325078815923559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-629386868881520562235270950239513438750000000000)
      constant := (4213603770646958829555489802680975602593398398649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree026.table
  base := (-75468048087292007144139795236016846667/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1259105955717863190407266613239895158750000000000)
      constant := (8431743862434996282504133508199236427370215670925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/5000000000000000000)
  centralHi := (249603131199392952461/100000000000000000000)
  directionLo := (25454624732791294161/10000000000000000000)
  directionHi := (254546247327912941611/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree027.table
  base := (-4268026194926070640008925161365720849591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2614123746097402696848398915485172142500000000000)
      constant := (18147302300786678710294822073432732617652253681001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree027.table
  base := (-1067128003781025058603458817813296987159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-653703434308585208448476022035590027812500000000)
      constant := (4539276135442808855549788862812363152581827773249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25454624732791294161/10000000000000000000)
  centralHi := (254546247327912941611/100000000000000000000)
  directionLo := (259395182979377396971/100000000000000000000)
  directionHi := (64848795744844349243/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree028.table
  base := (-2357703773999841869104806110623602183101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1355350008334361572377857015006145265000000000000)
      constant := (9748583124004191072873385003084501403392104504611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree028.table
  base := (-4715804934815633162570173053505855490079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2711415563032955286773274949804929905000000000000)
      constant := (19507722719155918162391544490866693415777875690369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259395182979377396971/100000000000000000000)
  centralHi := (64848795744844349243/25000000000000000000)
  directionLo := (66038781161662092001/25000000000000000000)
  directionHi := (52831024929329673601/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree029.table
  base := (-2558994893185349724427664722833158285417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1403638143620021796331514572269704458750000000000)
      constant := (10451813594058733166405328185243888383429008828087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree029.table
  base := (-511831442351540519230921293099854227853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1404008694415784869876322905733749849375000000000)
      constant := (10457481459534453177917268394213052995415915014415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66038781161662092001/25000000000000000000)
  centralHi := (52831024929329673601/20000000000000000000)
  directionLo := (134415399788554725471/50000000000000000000)
  directionHi := (268830799577109450943/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree030.table
  base := (-5478167929419436216769448792603151858353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2903852557811364040570344259066527305000000000000)
      constant := (22366385601214083550119595574067134420679973438383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree030.table
  base := (-1095686564054571079527065461531939581867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-2904619214630184192732016673130069492500000000000)
      constant := (22378525956811162406196512347326696836532946570185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134415399788554725471/50000000000000000000)
  centralHi := (268830799577109450943/100000000000000000000)
  directionLo := (8544579086364314279/3125000000000000000)
  directionHi := (273426530763658056929/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree031.table
  base := (-72472888736500195431412138334193673471/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-750107207095671122119414843398411423125000000000)
      constant := (5971301308673625844471010663736370833865865173620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree031.table
  base := (-2899023499629729137845693804565213504469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1500610520214399322855693767396319643125000000000)
      constant := (11949087930431497207244125853542543955451301393659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8544579086364314279/3125000000000000000)
  centralHi := (273426530763658056929/100000000000000000000)
  directionLo := (277946283748553293493/100000000000000000000)
  directionHi := (138973141874276646747/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree032.table
  base := (-3039234697082077292149240098971077147529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1548502549477002468192487244060382040000000000000)
      constant := (12729949868751372220440909338741283746150445647319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree032.table
  base := (-6078645181584086528411967177219292262937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3097822866227413098690758396455209080000000000000)
      constant := (25473726515053007747239767814141678028655445140807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277946283748553293493/100000000000000000000)
  centralHi := (138973141874276646747/50000000000000000000)
  directionLo := (141196853341189012781/50000000000000000000)
  directionHi := (282393706682378025563/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree033.table
  base := (-6321258181035521265777716091055775815599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3193581369525325384292289602647882467500000000000)
      constant := (27090322118982007160618927071219107963971380831089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree033.table
  base := (-1580350292135486058405083583218439384801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-798606173006506887917532314529444718437500000000)
      constant := (6776257781097759161081941624992222340657359448311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141196853341189012781/50000000000000000000)
  centralHi := (282393706682378025563/100000000000000000000)
  directionLo := (286772164789392714151/100000000000000000000)
  directionHi := (35846520598674089269/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree034.table
  base := (-3263562286119585670119798623306526184349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1645078820048322916099802358587500427500000000000)
      constant := (14388178217445575934189009303557669790957694262339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree034.table
  base := (-6527240773142315718634404052914788329599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3291026517824642004649500119780348667500000000000)
      constant := (28791973907175230455522160577020045123925935485089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286772164789392714151/100000000000000000000)
  centralHi := (35846520598674089269/12500000000000000000)
  directionLo := (291084770165284094427/100000000000000000000)
  directionHi := (72771192541321023607/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree035.table
  base := (-6696799863332829048831685605504133859009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3386733910667966280106919831702119242500000000000)
      constant := (30517911229781421600558266415247691993923486413599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree035.table
  base := (-837111776753982216690971960251880775121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-846907085905814114407217745360729615312500000000)
      constant := (7633615885658695004025086249714911846181309528662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291084770165284094427/100000000000000000000)
  centralHi := (72771192541321023607/25000000000000000000)
  directionLo := (295334407657417932813/100000000000000000000)
  directionHi := (147667203828708966407/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree036.table
  base := (-1366172178475225590608065869461696986979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3483310181239286728014234946229237630000000000000)
      constant := (32314914364579842832432937711801877116177833031345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree036.table
  base := (-1707734359752820126360960129898226258473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-871057542355467727652060460776372063750000000000)
      constant := (8083107000758009457804673329963847077577734699703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295334407657417932813/100000000000000000000)
  centralHi := (147667203828708966407/50000000000000000000)
  directionLo := (37440469679908942869/12500000000000000000)
  directionHi := (299523757439271542953/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree037.table
  base := (-1732440665842882752624691135081381023153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-894971612952651793980387515189089004375000000000)
      constant := (8541827234179593647944747836165000143134876151183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree037.table
  base := (-692982471767071782732062135114929358041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1790415997610242681793806352384029024375000000000)
      constant := (17092905238822096764645372300891082570963816244755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37440469679908942869/12500000000000000000)
  centralHi := (299523757439271542953/100000000000000000000)
  directionLo := (151827657390477797813/50000000000000000000)
  directionHi := (303655314780955595627/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree038.table
  base := (-6993864079016942900583231844570105596681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3676462722381927623828865175283474405000000000000)
      constant := (36075050062009016198022925818139581956278034043991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree038.table
  base := (-3496957174012061891325779995664645750319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1838716910509549908283491783215313921250000000000)
      constant := (18047283078952356148882672838224615750458459273009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151827657390477797813/50000000000000000000)
  centralHi := (303655314780955595627/100000000000000000000)
  directionLo := (307731407430088105217/100000000000000000000)
  directionHi := (153865703715044052609/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree039.table
  base := (-219482757447326482656145688094385008099/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-943259748238312017934045072452648198125000000000)
      constant := (9509525584058807659621851375430109767060213088712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree039.table
  base := (-28093955728322876410075213413087011397/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1887017823408857134773177214046598818125000000000)
      constant := (19029329850875365309362578416938257456577844233375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307731407430088105217/100000000000000000000)
  centralHi := (153865703715044052609/50000000000000000000)
  directionLo := (62350842189367270663/20000000000000000000)
  directionHi := (77938552736709088329/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree040.table
  base := (-701873844706716453739611147835795590239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1934807631762284259821747702168855590000000000000)
      constant := (20028218916443694502332972289469147712881286360645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree040.table
  base := (-3509385683913233607533267612485747182813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1935318736308164361262862644877883715000000000000)
      constant := (20039031616837012388336889115607649631284216637443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62350842189367270663/20000000000000000000)
  centralHi := (77938552736709088329/25000000000000000000)
  directionLo := (315725762279966939049/100000000000000000000)
  directionHi := (6314515245599338781/2000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree041.table
  base := (-3489955423389683863449688393147637713119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-1983095767047944483775405259432414783750000000000)
      constant := (21065017261899487577594827505364669743774584263809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree041.table
  base := (-6979937462625958213582006555538417302873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-3967239298414943175505096151418337223750000000000)
      constant := (42152754767295416697850243934555135293601131888103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315725762279966939049/100000000000000000000)
  centralHi := (6314515245599338781/2000000000000000000)
  directionLo := (159823985912196428107/50000000000000000000)
  directionHi := (63929594364878571243/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree042.table
  base := (-1381420875240387041885938704540250377171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4062767804667209415458125633391947955000000000000)
      constant := (44258875033360801964575135072248538796369687371905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree042.table
  base := (-3453562940919098313642790808647190657811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2031920562106778814242233506540453508750000000000)
      constant := (22141358480597983637140784809802797197157957481421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159823985912196428107/50000000000000000000)
  centralHi := (63929594364878571243/20000000000000000000)
  directionLo := (323522634162788530129/100000000000000000000)
  directionHi := (32352263416278853013/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree043.table
  base := (-6800428628901250865936179256449000959023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4159344075238529863365440747919066342500000000000)
      constant := (46442945655857459777093051285331699199722823680753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree043.table
  base := (-1360089199126152052409446882246787016601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4160442950012172081463837874743476811250000000000)
      constant := (46467936137598407381197915137359012815114909615555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323522634162788530129/100000000000000000000)
  centralHi := (32352263416278853013/10000000000000000000)
  directionLo := (65470287532532239213/20000000000000000000)
  directionHi := (163675718831330598033/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree044.table
  base := (-665997005123456047219312513520397969499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2127960172904925155636377931223092365000000000000)
      constant := (24341117790175842762288831109857277548039087369945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree044.table
  base := (-6659984068033401815823028079092994063173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4257044775810786534443208736406046605000000000000)
      constant := (48708401508367257065396523886858162395854550901403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65470287532532239213/20000000000000000000)
  centralHi := (163675718831330598033/50000000000000000000)
  directionLo := (331135973074495205699/100000000000000000000)
  directionHi := (3311359730744952057/1000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree045.table
  base := (-6485796831254910141912377583563473041363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4352496616381170759180070976973303117500000000000)
      constant := (50976736279280409355154728468290492999100617356493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree045.table
  base := (-6485808138459708319896475762970993521961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4353646601609400987422579598068616398750000000000)
      constant := (51004104564528221273088052700427303375000934562071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331135973074495205699/100000000000000000000)
  centralHi := (3311359730744952057/1000000000000000000)
  directionLo := (334877741255184753601/100000000000000000000)
  directionHi := (167438870627592376801/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree046.table
  base := (-156949068875852741548770105186416941881/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1112268221738122801771846522875105376250000000000)
      constant := (13331610256546243854893682813030338550542944411910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree046.table
  base := (-1569492967983347040124268322254369075127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1112562106852003860100487614932796548125000000000)
      constant := (13338759648690214465151406548330135271814402269897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334877741255184753601/100000000000000000000)
  centralHi := (167438870627592376801/50000000000000000000)
  directionLo := (84644540030779644631/25000000000000000000)
  directionHi := (13543126404924743141/4000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree047.table
  base := (-6036510248494815805168233208623977311157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4545649157523811654994701206027539892500000000000)
      constant := (55731344515301175908301431387669697407287861581227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree047.table
  base := (-6036517595896171811621297085136974271229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4546850253206629893381321321393755986250000000000)
      constant := (55761198305616933337595517235663589435876141358019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84644540030779644631/25000000000000000000)
  centralHi := (13543126404924743141/4000000000000000000)
  directionLo := (68447714187264947243/20000000000000000000)
  directionHi := (42779821367040592027/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree048.table
  base := (-5761472776779788629303732352517996554417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4642225428095132102902016320554658280000000000000)
      constant := (58191442561495357936464370564851645527600849287087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree048.table
  base := (-1440369673861079376798484912760934731553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1160863019751311086590173045764081445000000000000)
      constant := (14555644880493342358377762203252787870809629643583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68447714187264947243/20000000000000000000)
  centralHi := (42779821367040592027/12500000000000000000)
  directionLo := (345860243972503195961/100000000000000000000)
  directionHi := (172930121986251597981/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree049.table
  base := (-5452876736852384881578077300227812705139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4738801698666452550809331435081776667500000000000)
      constant := (60706731863576772957531416409307761372476358986029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree049.table
  base := (-2726440751267681454969069270311442469693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2370026952401929399670031522359447786875000000000)
      constant := (30369589475384506059276905497198822411758389183123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345860243972503195961/100000000000000000000)
  centralHi := (172930121986251597981/50000000000000000000)
  directionLo := (87361095919787533361/25000000000000000000)
  directionHi := (69888876735830026689/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree050.table
  base := (-1022148590072497696274758177198147236117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4835377969237772998716646549608895055000000000000)
      constant := (63277209817600526351635273419857495196397228178935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree050.table
  base := (-5110746786071518137994783139468728925549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4836655730602473252319433906381465367500000000000)
      constant := (63310993994655563904378474523255120259560073015539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87361095919787533361/25000000000000000000)
  centralHi := (69888876735830026689/20000000000000000000)
  directionLo := (352992133352972531953/100000000000000000000)
  directionHi := (176496066676486265977/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree051.table
  base := (-1183771960301365877654770777299090978549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1232988559952273361655990416034003360625000000000)
      constant := (16475718592400664124305261379823123423737839598539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree051.table
  base := (-4735090927180499883529234004799981368499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-4933257556401087705298804768044035161250000000000)
      constant := (65938022605017563297726069104797050597025681862989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352992133352972531953/100000000000000000000)
  centralHi := (176496066676486265977/50000000000000000000)
  directionLo := (356504579400131125263/100000000000000000000)
  directionHi := (22281536212508195329/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree052.table
  base := (-2162962182184917332038094766789595092791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2514265255190206947265638389331565915000000000000)
      constant := (34291861949719459247548943275757247040928649956201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree052.table
  base := (-2162963423100283775060394788364943743137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2514929691099851079139087814853302477500000000000)
      constant := (34310131583022054935217761452562188143407039523007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356504579400131125263/100000000000000000000)
  centralHi := (22281536212508195329/6250000000000000000)
  directionLo := (1439931020889242751/400000000000000000)
  directionHi := (359982755222310687751/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree053.table
  base := (-194163136930188993151405929043817343013/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (8139098806090672005679465026787500000000000)
      linear := (-456132678973988460523192585723589375000000000)
      constant := (6347432994763072890241105487621783032546091135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree053.table
  base := (-1941632366912985484102588465681753988919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16278197612181344011358930053575000000000000)
      linear := (-912506444997920365122382785932569375000000000)
      constant := (12701622357296580310337167541608389876753087201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1439931020889242751/400000000000000000)
  centralHi := (359982755222310687751/100000000000000000000)
  directionLo := (181713822384008330283/50000000000000000000)
  directionHi := (363427644768016660567/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree054.table
  base := (-3407111024335688306071117876538479124033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5221683051523054790345907007717368605000000000000)
      constant := (74110973050726506521905003396147752828786265400863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree054.table
  base := (-425889078473357405858513451674688926383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1305765758449232766059229338257936135625000000000)
      constant := (18537593827891843267341514448177639672069854303426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181713822384008330283/50000000000000000000)
  centralHi := (363427644768016660567/100000000000000000000)
  directionLo := (73368037156737227913/20000000000000000000)
  directionHi := (183420092891843069783/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree055.table
  base := (-2897475579532535682016939083960903894569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5318259322094375238253222122244486992500000000000)
      constant := (76957370869020676018047492282983571768435840984759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree055.table
  base := (-724369216924203307358493246588139311889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1329916214898886379304072053673578584062500000000)
      constant := (19249561274510207412596184272957585613911146910279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73368037156737227913/20000000000000000000)
  centralHi := (183420092891843069783/50000000000000000000)
  directionLo := (370221272795055656179/100000000000000000000)
  directionHi := (18511063639752782809/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree056.table
  base := (-1177180709638361736356999027025886447377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2707417796332847843080268618385802690000000000000)
      constant := (39929474978428376530481861128825868666119006989647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree056.table
  base := (-23543624538069203188304103479679952613/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1354066671348539992548914769089221032500000000000)
      constant := (19975330784345928016056444430420665422941850131075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370221272795055656179/100000000000000000000)
  centralHi := (18511063639752782809/5000000000000000000)
  directionLo := (186785879922822774499/50000000000000000000)
  directionHi := (373571759845645548999/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree057.table
  base := (-71110899975876913047936341525601404103/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5511411863237016134067852351298723767500000000000)
      constant := (82815709819520825465331253580865178090098657915825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree057.table
  base := (-888886664983789424378101815593793934631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2756434255596387211587514969009726961875000000000)
      constant := (41429804468190052401415179141846079601522341486441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186785879922822774499/50000000000000000000)
  centralHi := (373571759845645548999/100000000000000000000)
  directionLo := (376892463016115947157/100000000000000000000)
  directionHi := (188446231508057973579/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree058.table
  base := (-1167711940193412825895693336608462718437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5607988133808336581975167465825842155000000000000)
      constant := (85827650066789734802419502001650175546231717901307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree058.table
  base := (-291928151702572411951408744330111869379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1402367584247847219038600199920505929375000000000)
      constant := (21468275526504005476317850316236222900232315012669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376892463016115947157/100000000000000000000)
  centralHi := (188446231508057973579/50000000000000000000)
  directionLo := (380184162745551490569/100000000000000000000)
  directionHi := (38018416274555149057/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree059.table
  base := (-32761387681906618241602030656522389277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1426141101094914257470620645088240135625000000000)
      constant := (22223692597715381264204859519655238756724524702188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree059.table
  base := (-52418273777886334375285309742604038659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2853036081395001664566885830672296755625000000000)
      constant := (44470901169732517062113351210112876690632189823745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380184162745551490569/100000000000000000000)
  centralHi := (38018416274555149057/10000000000000000000)
  directionLo := (191723802986690750623/50000000000000000000)
  directionHi := (383447605973381501247/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree060.table
  base := (152814771063689522873736045942828232457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5801140674950977477789797694880078930000000000000)
      constant := (92017070548947191434720045477438976109465845634473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree060.table
  base := (152814342028683972291865384773196040261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5802673988588617782113142523007163305000000000000)
      constant := (92065709394724772402428233112323371249566864086629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191723802986690750623/50000000000000000000)
  centralHi := (383447605973381501247/100000000000000000000)
  directionLo := (386683508118589525677/100000000000000000000)
  directionHi := (193341754059294762839/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree061.table
  base := (863277450397838418164784406631490039489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-5897716945522297925697112809407197317500000000000)
      constant := (95194550349539219691313796337717411447365834161121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree061.table
  base := (431638553175371117576432491234326856777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2949637907193616117546256692334866549375000000000)
      constant := (47622411540460869852403934585408707218682351556953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386683508118589525677/100000000000000000000)
  centralHi := (193341754059294762839/50000000000000000000)
  directionLo := (48736569363883623571/12500000000000000000)
  directionHi := (389892554911068988569/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree062.table
  base := (803602313604329161260983318155881671901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-2997146608046809186802213961967157852500000000000)
      constant := (49213604820790171874537025605703348100169904718589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree062.table
  base := (401801087847072339727798616702295493933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1498969410046461672017971061583075723125000000000)
      constant := (24619785811877361367650218114902958996590451080237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48736569363883623571/12500000000000000000)
  centralHi := (389892554911068988569/100000000000000000000)
  directionLo := (196537702044202323919/50000000000000000000)
  directionHi := (393075404088404647839/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree063.table
  base := (2384595348744814322327030976403268918987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6090869486664938821511743038461434092500000000000)
      constant := (101715048305919968519635852392505416776906846617643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree063.table
  base := (298074390959862860172767086371548310999/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1523119866496115285262813776998718171562500000000)
      constant := (25442167443937151080496075107178872321697742914022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196537702044202323919/50000000000000000000)
  centralHi := (393075404088404647839/100000000000000000000)
  directionLo := (396232686969972552007/100000000000000000000)
  directionHi := (49529085871246569001/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree064.table
  base := (3195448863499858559987204775674575091519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6187445757236259269419058152988552480000000000000)
      constant := (105058066248575081653723502963157395111237494373791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree064.table
  base := (798862171590867307461404864208526197893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1547270322945768898507656492414360620000000000000)
      constant := (26278350642996819545640204127246964955751611456677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396232686969972552007/100000000000000000000)
  centralHi := (49529085871246569001/12500000000000000000)
  directionLo := (399365009919028723937/100000000000000000000)
  directionHi := (199682504959514361969/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree065.table
  base := (4039764578706664405134520323277087009399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6284022027807579717326373267515670867500000000000)
      constant := (108456263395414529198944892999475406174772727137111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree065.table
  base := (1009941109201228301041304483179071207197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1571420779395422511752499207830003068437500000000)
      constant := (27128335390590174060836696670173094848039716817333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399365009919028723937/100000000000000000000)
  centralHi := (199682504959514361969/50000000000000000000)
  directionLo := (25154559731398566149/6250000000000000000)
  directionHi := (80494591140475411677/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree066.table
  base := (983508405361895200123072035431586613113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6380598298378900165233688382042789255000000000000)
      constant := (111909639687966027248795634109654830733350762396285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree066.table
  base := (4917541913160659199225173155759226322653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6382284943380304499989367692982582067500000000000)
      constant := (111968486688610824044722568342086643898915083304317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25154559731398566149/6250000000000000000)
  centralHi := (80494591140475411677/20000000000000000000)
  directionLo := (405557084756251324913/100000000000000000000)
  directionHi := (202778542378125662457/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree067.table
  base := (145719520975435383048370621522372071591/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1619293642237555153285250874142476910625000000000)
      constant := (28854548770027194262417766170516984276340106269990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree067.table
  base := (2914390374008605165497887171428393335357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3239443384589459476484369277322575930625000000000)
      constant := (57739418952394558707334156800908804658325595802573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405557084756251324913/100000000000000000000)
  centralHi := (202778542378125662457/50000000000000000000)
  directionLo := (408617936366198780251/100000000000000000000)
  directionHi := (102154484091549695063/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree068.table
  base := (677348072444377493671140698877736134871/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3286875419760770530524159305548513015000000000000)
      constant := (59490964767732317806592525675004017436269011704595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree068.table
  base := (6773480651594863659014475940691576479531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6575488594977533405948109416307721655000000000000)
      constant := (119044395174655874780877979089348180673009565819659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408617936366198780251/100000000000000000000)
  centralHi := (102154484091549695063/25000000000000000000)
  directionLo := (411656029768000034451/100000000000000000000)
  directionHi := (102914007442000008613/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree069.table
  base := (7751641453651324394661649895866895607923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6670327110092861508955633725624144417500000000000)
      constant := (122600843025340300141649905117804274395961944731347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree069.table
  base := (7751641395345783464351559543468960776971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6672090420776147858927480277970291448750000000000)
      constant := (122665158469629020596286266593935786279433723727819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411656029768000034451/100000000000000000000)
  centralHi := (102914007442000008613/25000000000000000000)
  directionLo := (414671865175989707341/100000000000000000000)
  directionHi := (207335932587994853671/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree070.table
  base := (4381631422836518506249936038752137794019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3383451690332090978431474420075631402500000000000)
      constant := (63137467763552063376102276907733611873615103396291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree070.table
  base := (8763262799017266778776430008236181852533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-6768692246574762311906851139632861242500000000000)
      constant := (126341127767166243936817474652836872305507600335637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414671865175989707341/100000000000000000000)
  centralHi := (207335932587994853671/50000000000000000000)
  directionLo := (104416481186136223931/25000000000000000000)
  directionHi := (16706636989781795829/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree071.table
  base := (4904172378887096901591449371732329671977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3431739825617751202385131977339190596250000000000)
      constant := (65002103511452892212885390191396840998791356239753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree071.table
  base := (2452086180112031131128803454177779264299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1716323518093344191221555500323857759062500000000)
      constant := (32518075762372234785193205346576111083727325758211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104416481186136223931/25000000000000000000)
  centralHi := (16706636989781795829/4000000000000000000)
  directionLo := (210319336733987381053/50000000000000000000)
  directionHi := (420638673467974762107/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree072.table
  base := (2721721769344214531434964969535591550097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1740013980451705713169394767301374895000000000000)
      constant := (33447164374666583483338597837936645174067848720433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree072.table
  base := (1088688704752076399990403466969361030103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3480947949085995608932796431479000415000000000000)
      constant := (66929342151287868678486046487300659869155973986835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210319336733987381053/50000000000000000000)
  centralHi := (420638673467974762107/100000000000000000000)
  directionLo := (423590560023567038343/100000000000000000000)
  directionHi := (52948820002945879793/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree073.table
  base := (11998889715690006256730086061504296270009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7056632192378143300584894183732617967500000000000)
      constant := (137628286943281615220315019282838654008300681565401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree073.table
  base := (11998889691813546063683800084505912784091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7058497723970605670844963724620570623750000000000)
      constant := (137700271515368673577867028495240077899124175289499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423590560023567038343/100000000000000000000)
  centralHi := (52948820002945879793/12500000000000000000)
  directionLo := (21326100878105965013/5000000000000000000)
  directionHi := (426522017562119300261/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree074.table
  base := (13144352602685061591714882622072523268809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7153208462949463748492209298259736355000000000000)
      constant := (141523095347993890281104205888627849597812863178601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree074.table
  base := (13144352583594206262034575994807865047031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7155099549769220123824334586283140417500000000000)
      constant := (141597064679147066444050042895870526375181407827159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21326100878105965013/5000000000000000000)
  centralHi := (426522017562119300261/100000000000000000000)
  directionLo := (214716732224949378571/50000000000000000000)
  directionHi := (429433464449898757143/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree075.table
  base := (14323275683132668919890228491987658591103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7249784733520784196399524412786854742500000000000)
      constant := (145473082705896204175259313015222438001928551126367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree075.table
  base := (14323275667871017971359821822325818054667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7251701375567834576803705447945710211250000000000)
      constant := (145549063787033678724746457469605998115978316585163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214716732224949378571/50000000000000000000)
  centralHi := (429433464449898757143/100000000000000000000)
  directionLo := (54040663120703624369/12500000000000000000)
  directionHi := (432325304965628994953/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree076.table
  base := (15535658913476563303824470473578431304239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7346361004092104644306839527313973130000000000000)
      constant := (149478249011541432666956521141296434087829732873871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree076.table
  base := (242744670332472371771378725772713000537/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1837075800341612257445769077402070001250000000000)
      constant := (37389067208401302990025976218913129594571773129488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54040663120703624369/12500000000000000000)
  centralHi := (432325304965628994953/100000000000000000000)
  directionLo := (435197929955791229727/100000000000000000000)
  directionHi := (13599935311118475929/3125000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree077.table
  base := (16781502259367729806338232155293358783447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7442937274663425092214154641841091517500000000000)
      constant := (153538594260633905500498810351482555741270293478583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree077.table
  base := (16781502249619536078624631803572905220137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7444905027165063482762447171270849798750000000000)
      constant := (153618679814585092889559272604672600945255453229993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435197929955791229727/100000000000000000000)
  centralHi := (13599935311118475929/3125000000000000000)
  directionLo := (43805171745124732959/10000000000000000000)
  directionHi := (438051717451247329591/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree078.table
  base := (722432227748775720206647832509071621159/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7539513545234745540121469756368209905000000000000)
      constant := (157654118449786164382919920788743989482038653193775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree078.table
  base := (9030402842965260063797665580761723362811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3770753426481838967870909016466709796250000000000)
      constant := (78868148363300583044921373628866785939746880263579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43805171745124732959/10000000000000000000)
  centralHi := (438051717451247329591/100000000000000000000)
  directionLo := (1102217583119846961/250000000000000000)
  directionHi := (440887033247938784401/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree079.table
  base := (19373569195172830806090217177069353681517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7636089815806065988028784870895328292500000000000)
      constant := (161824821576327098443423921476295156501939534764813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree079.table
  base := (3874713837790098294999391125106308285037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7638108678762292388721188894595989386250000000000)
      constant := (161909119566994580225459838979567489129758155330465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1102217583119846961/250000000000000000)
  centralHi := (440887033247938784401/100000000000000000000)
  directionLo := (2218521157270934919/500000000000000000)
  directionHi := (443704231454186983801/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree080.table
  base := (20719792746887241340788255997405295633197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7732666086377386435936099985422446680000000000000)
      constant := (166050703638150605606008212772919100997781548256333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree080.table
  base := (1294987046369822730469630220977731376109/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1933677626140226710425139939064639795000000000000)
      constant := (41534287083417263080147122140390259452601833393204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2218521157270934919/500000000000000000)
  centralHi := (443704231454186983801/100000000000000000000)
  directionLo := (446503655006913004801/100000000000000000000)
  directionHi := (223251827503456502401/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree081.table
  base := (22099476335585218711442935501178861661027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7829242356948706883843415099949565067500000000000)
      constant := (170331764633596220273846167324119531059898477835203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree081.table
  base := (5524869082904000540321125503478112817323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-1957828082589880323669982654480282243437500000000)
      constant := (42605095756242994857574217558697221762429311602947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446503655006913004801/100000000000000000000)
  centralHi := (223251827503456502401/50000000000000000000)
  directionLo := (449285636158907314429/100000000000000000000)
  directionHi := (44928563615890731443/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree082.table
  base := (11756309975399924743634452020074737586901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-3962909313760013665875365107238341727500000000000)
      constant := (87334002280677477800938266092041086215364432153589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree082.table
  base := (940504797905217056749851520919558334723/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-7927914156158135747659301479583698767500000000000)
      constant := (174758823639600669322933713938342864151622483413675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449285636158907314429/100000000000000000000)
  centralHi := (44928563615890731443/10000000000000000000)
  directionLo := (452050496939109335321/100000000000000000000)
  directionHi := (226025248469554667661/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree083.table
  base := (24959223584280844724313235164068338410579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8022394898091347779658045329003801842500000000000)
      constant := (179059423420395034670666204730884326539424831934131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree083.table
  base := (12479611790875216933573029262541017548643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4012257990978375100319336170623134280625000000000)
      constant := (89576235088264191634780303243247767714513169973427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452050496939109335321/100000000000000000000)
  centralHi := (226025248469554667661/50000000000000000000)
  directionLo := (90959709917540382051/20000000000000000000)
  directionHi := (28424909349231369391/6250000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree084.table
  base := (211514297836208933997343785488272288623/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8118971168662668227565360443530920230000000000000)
      constant := (183506021209903309718408116882287458396006611705875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree084.table
  base := (13219643613753087550393939997873309447977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4060558903877682326809021601454419177500000000000)
      constant := (91800661317473002604797130371650916174740375703753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90959709917540382051/20000000000000000000)
  centralHi := (28424909349231369391/6250000000000000000)
  directionLo := (114382524241921187007/25000000000000000000)
  directionHi := (457530096967684748029/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree085.table
  base := (27952810881412304700446823170158154930339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8215547439233988675472675558058038617500000000000)
      constant := (188007797929239055853627109528506075278989775936771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree085.table
  base := (13976405439900040963122090910869379038181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4108859816776989553298707032285704074375000000000)
      constant := (94052690507108017934810985784679024841289571099509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114382524241921187007/25000000000000000000)
  centralHi := (457530096967684748029/100000000000000000000)
  directionLo := (460245432954462529257/100000000000000000000)
  directionHi := (230122716477231264629/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree086.table
  base := (29499794535903349075350098378543562986791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8312123709805309123379990672585157005000000000000)
      constant := (192564753577897525537517049010238684928242396209799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree086.table
  base := (29499794534616726505484460317226483771557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8314321459352593559576784926233977942500000000000)
      constant := (192664645313836307896103269407301424861956461154373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460245432954462529257/100000000000000000000)
  centralHi := (230122716477231264629/50000000000000000000)
  directionLo := (462944842804866245097/100000000000000000000)
  directionHi := (231472421402433122549/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree087.table
  base := (124320952759282519343484712197647819957/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4204349990188314785643652893556137696250000000000)
      constant := (98588444077740601086168568505950250878457677746625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree087.table
  base := (31080238188793988951561796656494446906689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8410923285151208012556155787896547736250000000000)
      constant := (197279115533411368191819834818663516272855344521921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462944842804866245097/100000000000000000000)
  centralHi := (231472421402433122549/50000000000000000000)
  directionLo := (465628603506919420913/100000000000000000000)
  directionHi := (232814301753459710457/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree088.table
  base := (6538828368132332906466980613862865899829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8505276250947950019194620901639393780000000000000)
      constant := (201844201661677126581699529918769900617540699636905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree088.table
  base := (32694141839842580304086184321078867368241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8507525110949822465535526649559117530000000000000)
      constant := (201948791672629907551411952347538574509270994288849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465628603506919420913/100000000000000000000)
  centralHi := (232814301753459710457/50000000000000000000)
  directionLo := (234148492055781574119/50000000000000000000)
  directionHi := (468296984111563148239/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree089.table
  base := (17170752743228554723183064547651039071307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4300926260759635233550968008083256083750000000000)
      constant := (103283347048119506823259436134508243896811062982123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree089.table
  base := (1373660219432148175846041963203702588401/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8604126936748436918514897511221687323750000000000)
      constant := (206673673731246959927191127109871280767952347177225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234148492055781574119/50000000000000000000)
  centralHi := (468296984111563148239/100000000000000000000)
  directionLo := (235475123023732213191/50000000000000000000)
  directionHi := (470950246047464426383/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree090.table
  base := (140712223147101457672773349758259553/39062500000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2174607198022647728752312782673407638750000000000)
      constant := (52836091364743286823032023141197568083281848688000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree090.table
  base := (9005582281284200140006931195509165193013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2175182190636762842873567093221064279375000000000)
      constant := (52863440427267465897319428331525897190534479650357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235475123023732213191/50000000000000000000)
  centralHi := (470950246047464426383/100000000000000000000)
  directionLo := (236794321709975204287/50000000000000000000)
  directionHi := (18943545736798016343/4000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree091.table
  base := (9434153189261665211543270620469812578233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2198751265665477840729141561305187235625000000000)
      constant := (54044303937431813932514649494655565558264279002937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree091.table
  base := (37736612756631011548768976628807329200903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8797330588345665824473639234546826911250000000000)
      constant := (216289055605947189349116543002421615799124395018567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236794321709975204287/50000000000000000000)
  centralHi := (18943545736798016343/4000000000000000000)
  directionLo := (476212423295036048647/100000000000000000000)
  directionHi := (59526552911879506081/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree092.table
  base := (39484356379666815379167977731197384676089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-8891581333233231810823881359747867330000000000000)
      constant := (221065244968381737428453658345151070933228120858521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree092.table
  base := (9871089094833840953317392185294731548221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2223483103536070069363252524052349176250000000000)
      constant := (55294888855440002235150999733136234287281447119069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476212423295036048647/100000000000000000000)
  centralHi := (59526552911879506081/12500000000000000000)
  directionLo := (478821825969443718657/100000000000000000000)
  directionHi := (239410912984721859329/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree093.table
  base := (10316389998191996206498618135472833346047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2247039400951138064682799118568746429375000000000)
      constant := (56502113278710685312881364132356832162068485489983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree093.table
  base := (20632779996251853177380502552240547646911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4495267119971447365216190478935983249375000000000)
      constant := (113062630578207504550558626687790170765267685838479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478821825969443718657/100000000000000000000)
  centralHi := (239410912984721859329/50000000000000000000)
  directionLo := (481417085227450046723/100000000000000000000)
  directionHi := (120354271306862511681/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree094.table
  base := (10770055898940496060801472319495030958937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2271183468593968176659627897200526026250000000000)
      constant := (57751710047259177272702264281886881732732591203193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree094.table
  base := (10770055898887822425879994859649083046079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2271784016435377295852937954883634073125000000000)
      constant := (57781543202459765340194922169186460748303390693631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481417085227450046723/100000000000000000000)
  centralHi := (120354271306862511681/25000000000000000000)
  directionLo := (483998428585336996717/100000000000000000000)
  directionHi := (241999214292668498359/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree095.table
  base := (1797133887527539258593834392022771789091/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9181310144947193154545826703329222492500000000000)
      constant := (236060406190906072040859693543765643425652155862475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree095.table
  base := (44928347188020525426464424536182788012853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9183737891540123636391122681197106086250000000000)
      constant := (236182290381974939943977750816027612871474909112117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483998428585336996717/100000000000000000000)
  centralHi := (241999214292668498359/50000000000000000000)
  directionLo := (48656607752417061789/10000000000000000000)
  directionHi := (486566077524170617891/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree096.table
  base := (23404965384843929125311409209590441523711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4638943207759256801226570908928170440000000000000)
      constant := (120584575560202928214155711680910285956239679043679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree096.table
  base := (46809930769553986223345373509460863955539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9280339717338738089370493542859675880000000000000)
      constant := (241293613872777945175187654421662014191778226059571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48656607752417061789/10000000000000000000)
  centralHi := (486566077524170617891/100000000000000000000)
  directionLo := (489120247711581519421/100000000000000000000)
  directionHi := (244560123855790759711/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree097.table
  base := (304531089624873811171783738218732552439/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2343615671522458512590114233095864816875000000000)
      constant := (61583268744375251869119950522896879973919669246840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree097.table
  base := (48724974339873116540630342237701756190497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9376941543137352542349864404522245673750000000000)
      constant := (246460143282213241039226514884610088440578328976033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489120247711581519421/100000000000000000000)
  centralHi := (244560123855790759711/50000000000000000000)
  directionLo := (491661149213175599523/100000000000000000000)
  directionHi := (122915287303293899881/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree098.table
  base := (25336738949423235095030081479482759423661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4735519478330577249133886023455288827500000000000)
      constant := (125776088881082139494534747630802454983770479169229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree098.table
  base := (50673477898761446908394263120252771745199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9473543368935966995329235266184815467500000000000)
      constant := (251681878610253755974801402382443753768256975143311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491661149213175599523/100000000000000000000)
  centralHi := (122915287303293899881/25000000000000000000)
  directionLo := (247094493347080772367/50000000000000000000)
  directionHi := (98837797338832308947/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree099.table
  base := (52655441446119107729582076425423862744317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9567615227232474946175087161437696042500000000000)
      constant := (256826459474374569462303060802907123064929171674013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree099.table
  base := (13163860361512840045717006468469183209577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2392536298683645362077151531961846315312500000000)
      constant := (64239704964219631966891228112289180863919501401153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247094493347080772367/50000000000000000000)
  centralHi := (98837797338832308947/20000000000000000000)
  directionLo := (496703959611742808549/100000000000000000000)
  directionHi := (9934079192234856171/2000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree100.table
  base := (54670864981667635516032552355148862887839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9664191497803795394082402275964814430000000000000)
      constant := (262155920114115610296189175129919210999184209654271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree100.table
  base := (54670864981613658985066524710748941814417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9666747020533195901287976989509955055000000000000)
      constant := (262290967022071399359321028416312698392476722852913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496703959611742808549/100000000000000000000)
  centralHi := (9934079192234856171/2000000000000000000)
  directionLo := (499206262398785904921/100000000000000000000)
  directionHi := (249603131199392952461/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree101.table
  base := (56719748505392342688453017977010992404177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9760767768375115841989717390491932817500000000000)
      constant := (267540559681374931701408609081714401186668007085553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree101.table
  base := (28359874252674671122513302256970012502233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-4881674423165905177133673925586262424375000000000)
      constant := (133839160052909994713424852428080377929255214088937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499206262398785904921/100000000000000000000)
  centralHi := (249603131199392952461/50000000000000000000)
  directionLo := (250848042319621831291/50000000000000000000)
  directionHi := (501696084639243662583/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree102.table
  base := (2352083680688695073806304078849874300177/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9857344038946436289897032505019051205000000000000)
      constant := (272980378176143047615367104852523327999234205738825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree102.table
  base := (2352083680687324954725233472770123978249/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9859950672130424807246718712835094642500000000000)
      constant := (273120879108114882829629280514474378876380426369025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250848042319621831291/50000000000000000000)
  centralHi := (501696084639243662583/100000000000000000000)
  directionLo := (4033388889886250843/800000000000000000)
  directionHi := (31510850702236334711/6250000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree103.table
  base := (60917895517085607576873303601166042365281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9953920309517756737804347619546169592500000000000)
      constant := (278475375598412813338274620108718864482823143201409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree103.table
  base := (12183579103411665042968800171834659499407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-9956552497929039260226089574497664436250000000000)
      constant := (278618644028948991365962265484565970295041363615115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4033388889886250843/800000000000000000)
  centralHi := (31510850702236334711/6250000000000000000)
  directionLo := (15832469455313285853/3125000000000000000)
  directionHi := (506639022570025147297/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree104.table
  base := (63067159004954579158441486295683725919129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10050496580089077185711662734073287980000000000000)
      constant := (284025551948178919378837691316784430739062328065081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree104.table
  base := (31533579502466425456116304080003965588393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5026577161863826856602730218080117115000000000000)
      constant := (142085807434158525305010166633464066308208012911177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15832469455313285853/3125000000000000000)
  centralHi := (506639022570025147297/100000000000000000000)
  directionLo := (509092494655825883221/100000000000000000000)
  directionHi := (254546247327912941611/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree105.table
  base := (13049976496158664426233156284539334542063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10147072850660397633618977848600406367500000000000)
      constant := (289630907225437492712377144009433567146620988929035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree105.table
  base := (65249882480776018899386846125613726013717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10149756149526268166184831297822804023750000000000)
      constant := (289779791626215223478944635823201424563028642510613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509092494655825883221/100000000000000000000)
  centralHi := (254546247327912941611/50000000000000000000)
  directionLo := (511534199285906748579/100000000000000000000)
  directionHi := (25576709964295337429/5000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree106.table
  base := (33733032972289921078321474709879919023631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16278197612181344011358930053575000000000000)
      linear := (-1823362250130245297530490025476597500000000000)
      constant := (52561666327907757696363719467967659812351075751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree106.table
  base := (33733032972283032011651889737167708250729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16278197612181344011358930053575000000000000)
      linear := (-1823844424230132185682485254447378750000000000)
      constant := (52588674671171375584518088154425412523405705809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511534199285906748579/100000000000000000000)
  centralHi := (25576709964295337429/5000000000000000000)
  directionLo := (20558572166889622403/4000000000000000000)
  directionHi := (128491076043060140019/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree107.table
  base := (69715709396299142895618073879954252716261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10340225391803038529433608077654643142500000000000)
      constant := (301007154562421914021696296715023665422291212650629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree107.table
  base := (6971570939628817268696602664779822172447/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5171479900561748536071786510573971805625000000000)
      constant := (150580881448795945846890518945100693912512802247915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20558572166889622403/4000000000000000000)
  centralHi := (128491076043060140019/25000000000000000000)
  directionLo := (516382973080481295267/100000000000000000000)
  directionHi := (129095743270120323817/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree108.table
  base := (14399762567188333986507074456325180586671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10436801662374358977340923192181761530000000000000)
      constant := (306778046622144691692624806428224442537508977355595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree108.table
  base := (71998812835932936168423975428626045322039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10439561626922111525122943882810513405000000000000)
      constant := (306935557411067357808860730151466473836940037778071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516382973080481295267/100000000000000000000)
  centralHi := (129095743270120323817/25000000000000000000)
  directionLo := (259395182979377396971/50000000000000000000)
  directionHi := (518790365958754793943/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree109.table
  base := (74315376263502086640052644930106586006781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10533377932945679425248238306708879917500000000000)
      constant := (312604117609353448355068506188693482718261332394909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree109.table
  base := (74315376263495133983239899761879358474361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10536163452720725978102314744473083198750000000000)
      constant := (312764557843066533507945581562604502192131093761529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259395182979377396971/50000000000000000000)
  centralHi := (518790365958754793943/100000000000000000000)
  directionLo := (521186639061095252641/100000000000000000000)
  directionHi := (260593319530547626321/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree110.table
  base := (76665399678978311708287919296572018540829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10629954203516999873155553421235998305000000000000)
      constant := (318485367524047923721477105861663983312289600376381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree110.table
  base := (76665399678972777397133433207583706251999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10632765278519340431081685606135652992500000000000)
      constant := (318648764193589170080942732713899518384069850168511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521186639061095252641/100000000000000000000)
  centralHi := (260593319530547626321/50000000000000000000)
  directionLo := (261785972532898539677/50000000000000000000)
  directionHi := (104714389013159415871/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree111.table
  base := (79048883082370762916178133109110842526009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10726530474088320321062868535763116692500000000000)
      constant := (324421796366228170039070973842635530833630904749401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree111.table
  base := (15809776616473271594298502954994175763301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10729367104317954884061056467798222786250000000000)
      constant := (324588176462635329002268171388609216372915227565945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261785972532898539677/50000000000000000000)
  centralHi := (104714389013159415871/20000000000000000000)
  directionLo := (262973216594467890637/50000000000000000000)
  directionHi := (21037857327557431251/4000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree112.table
  base := (40732913236840881718636170876277191612021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5411553372329820384485091825145117540000000000000)
      constant := (165206702067947238921373506657233914585354432517269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree112.table
  base := (40732913236839128838980940380461539323577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5412984465058284668520213664730396290000000000000)
      constant := (165291397325102654080039300398780718346959945272153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262973216594467890637/50000000000000000000)
  centralHi := (21037857327557431251/4000000000000000000)
  directionLo := (528310249293296736009/100000000000000000000)
  directionHi := (52831024929329673601/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree113.table
  base := (16783245970583015242461959664515908749967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-10919683015230961216877498764817353467500000000000)
      constant := (336460190833047317723951212551547899936176258934315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree113.table
  base := (41958114926456143154634951161007319564963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5461285377957591895009899095561681186875000000000)
      constant := (168316309378149792002552913476699852235425068833907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528310249293296736009/100000000000000000000)
  centralHi := (52831024929329673601/10000000000000000000)
  directionLo := (265331767996468432311/50000000000000000000)
  directionHi := (530663535992936864623/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree114.table
  base := (86400093220075539208816460754474917272023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11016259285802281664784813879344471855000000000000)
      constant := (342562156457687294716430166447498429659231470376247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree114.table
  base := (86400093220073319162110683240834574095273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11019172581713798242999169052785932167500000000000)
      constant := (342737648780918766239463137864487568870356228695497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265331767996468432311/50000000000000000000)
  centralHi := (530663535992936864623/100000000000000000000)
  directionLo := (133251608188397827229/25000000000000000000)
  directionHi := (533006432753591308917/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree115.table
  base := (1778348331503375602720892239050181821103/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5556417778186801056346064496935795121250000000000)
      constant := (174359650504907556309313603037205341890965139909175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree115.table
  base := (11114677071895876710580268541063823615653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2778943601878103173994634978612125490312500000000)
      constant := (87224471181015890595181551899751270560314315037634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133251608188397827229/25000000000000000000)
  centralHi := (533006432753591308917/100000000000000000000)
  directionLo := (107067815197825029483/20000000000000000000)
  directionHi := (66917384498640643427/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree116.table
  base := (91468199918200993717135898538674767129671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11209411826944922560599444108398708630000000000000)
      constant := (354931624489431546139452922233449645781930651998119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree116.table
  base := (22867049979549897072417571796276851460977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2803094058327756787239477694027767938750000000000)
      constant := (88778331646433687525105736068118913277957437060753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107067815197825029483/20000000000000000000)
  centralHi := (66917384498640643427/12500000000000000000)
  directionLo := (107532319830843780377/20000000000000000000)
  directionHi := (268830799577109450943/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree117.table
  base := (47026221624589384097982258919353719533719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5652994048758121504253379611462913508750000000000)
      constant := (180599563448268709600659814711228481517245591409591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree117.table
  base := (94052443249177650090157773785436615143651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11308978059109641601937281637773641548750000000000)
      constant := (361383974365933155680724225168262817835309343154339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107532319830843780377/20000000000000000000)
  centralHi := (268830799577109450943/50000000000000000000)
  directionLo := (4319793062667728253/800000000000000000)
  directionHi := (269987066416733015813/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree118.table
  base := (19334029313621790115216193233245742609349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11402564368087563456414074337452945405000000000000)
      constant := (367521808231133588086992533896110537347628562813305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree118.table
  base := (96670146568108061117677555478384935855637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11405579884908256054916652499436211342500000000000)
      constant := (367709828064659637283792064948042254212622490989493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4319793062667728253/800000000000000000)
  centralHi := (269987066416733015813/50000000000000000000)
  directionLo := (271138402413525366663/50000000000000000000)
  directionHi := (542276804827050733327/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree119.table
  base := (24830327468749635578287484887090921895449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2874785159664720976080347362995015948125000000000)
      constant := (93474917123305232098734829673725740920150950865561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree119.table
  base := (19864261974999566959128479632735506214949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11502181710706870507896023361098781136250000000000)
      constant := (374090887681915072004774604751310216380856418005305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271138402413525366663/50000000000000000000)
  centralHi := (542276804827050733327/100000000000000000000)
  directionLo := (272284870116582555761/50000000000000000000)
  directionHi := (544569740233165111523/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree120.table
  base := (25501483292463654734041213690466674196931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2898929227307551088057176141626795545000000000000)
      constant := (95083176920700081246800076301324791534097676228259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree120.table
  base := (5100296658492702809141967573525684198081/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-2899695884126371240218848555690337732500000000000)
      constant := (95131788304425086474375821991128001542811923203045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272284870116582555761/50000000000000000000)
  centralHi := (544569740233165111523/100000000000000000000)
  directionLo := (8544579086364314279/1562500000000000000)
  directionHi := (546853061527316113857/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree121.table
  base := (104724016452684268455837543299224613817149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11692293179801524800136019681034300567500000000000)
      constant := (386820925799872664286773141600003660410663743376861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree121.table
  base := (10472401645268382087777810253535778369833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5847692681152049706927382542211960361875000000000)
      constant := (193509312336008173166950942611241866680801433726685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8544579086364314279/1562500000000000000)
  centralHi := (546853061527316113857/100000000000000000000)
  directionLo := (549126888638664495413/100000000000000000000)
  directionHi := (274563444319332247707/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree122.table
  base := (53737779861747272254619501515982567552519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5894434725186422624021667397780709477500000000000)
      constant := (196682161422219414208952759164774893934463506802791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree122.table
  base := (107475559723494188558544879767064455571539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11791987188102713866834135946086490517500000000000)
      constant := (393565302044863956193704364747974040465558620283571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549126888638664495413/100000000000000000000)
  centralHi := (274563444319332247707/50000000000000000000)
  directionLo := (551391339023530449353/100000000000000000000)
  directionHi := (275695669511765224677/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree123.table
  base := (110260562982292431049793041256036462498881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11885445720944165695950649910088537342500000000000)
      constant := (399962898816499690790243816534803302404696470931809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree123.table
  base := (55130281491146073993847946380710466508773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5944294506950664159906753403874530155625000000000)
      constant := (200083592668122024743992374223404487724691109146997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551391339023530449353/100000000000000000000)
  centralHi := (275695669511765224677/50000000000000000000)
  directionLo := (553646527736193381983/100000000000000000000)
  directionHi := (17301453991756043187/3125000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree124.table
  base := (113079026229084816069834867320622707295811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-11982021991515486143857965024615655730000000000000)
      constant := (406616653716056112812589713413681191543710695500579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree124.table
  base := (452316104916338363942791352063350702527/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-5992595419849971386396438834705815052500000000000)
      constant := (203412137273078744052144440562236390106664703587875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553646527736193381983/100000000000000000000)
  centralHi := (17301453991756043187/3125000000000000000)
  directionLo := (555892567497106586987/100000000000000000000)
  directionHi := (138973141874276646747/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree125.table
  base := (57965474731939236188790959093518410222959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6039299131043403295882640069571387058750000000000)
      constant := (206662793771554470744438988316727482850435003607951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree125.table
  base := (23186189892775658681551495985481594426601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12081792665498557225772248531074199898750000000000)
      constant := (413536569674605119427606458725809334529909532834445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555892567497106586987/100000000000000000000)
  centralHi := (138973141874276646747/25000000000000000000)
  directionLo := (558129568758641256001/100000000000000000000)
  directionHi := (279064784379320628001/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree126.table
  base := (59408166343340021935922364221331878991583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6087587266329063519836297626834946252500000000000)
      constant := (210044850148829503850849409678719906662034705281087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree126.table
  base := (59408166343339950788864728579078193277733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6089197245648585839375809696368384846250000000000)
      constant := (210152035360793887321901235436085537041340899058437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558129568758641256001/100000000000000000000)
  centralHi := (279064784379320628001/50000000000000000000)
  directionLo := (280178819884234161749/50000000000000000000)
  directionHi := (560357639768468323499/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree127.table
  base := (121735175897496036090046588163199308567701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12271750803229447487579910368197010892500000000000)
      constant := (426908991979707125030238068619201021062598758964789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree127.table
  base := (30433793974373980740732926991528113229679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3068749079273946532932747563599834871562500000000)
      constant := (106781694421776566893353595780660180635760842249031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280178819884234161749/50000000000000000000)
  centralHi := (560357639768468323499/100000000000000000000)
  directionLo := (140644221657670264393/25000000000000000000)
  directionHi := (562576886630681057573/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree128.table
  base := (24937495819266562013396981438676469800381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12368327073800767935487225482724129280000000000000)
      constant := (433783462589254088982256999712445202187797899326545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree128.table
  base := (15585934887041590016735818392837687005423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3092899535723600146177590279015477320000000000000)
      constant := (108501172642790348479065110657032768153680281217694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140644221657670264393/25000000000000000000)
  centralHi := (562576886630681057573/100000000000000000000)
  directionLo := (141196853341189012781/25000000000000000000)
  directionHi := (4518299306918048409/800000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree129.table
  base := (31918310570799144687033095261925418021731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3116225836093022095848635149312811916875000000000)
      constant := (110178278031575169136385403200416729305901257255459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree129.table
  base := (31918310570799126814508584777769400158093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3117049992173253759422432994431119768437500000000)
      constant := (110234452343438482703236325450343888474730676669477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141196853341189012781/25000000000000000000)
  centralHi := (4518299306918048409/800000000000000000)
  directionLo := (566989321962445318303/100000000000000000000)
  directionHi := (17718416311326416197/3125000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree130.table
  base := (65346232729046702681938340187078332413351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6280739807471704415650927855889183027500000000000)
      constant := (223848970295423822992292939625002634190523312837639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree130.table
  base := (130692465458093348538001776041254956740133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12564801794491629490669102839387048867500000000000)
      constant := (447926134094884636649550647222916442126606888772037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566989321962445318303/100000000000000000000)
  centralHi := (17718416311326416197/3125000000000000000)
  directionLo := (284591356221343769327/50000000000000000000)
  directionHi := (113836542488537507731/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree131.table
  base := (133745148621029203299188576272085523266407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12658055885514729279209170826305484442500000000000)
      constant := (454737947982895736824292503971079458695713220286023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree131.table
  base := (66872574310514579066124180453713005166517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6330701810145121971824236850524809330625000000000)
      constant := (227484832367277125523855644680950112388993819679813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284591356221343769327/50000000000000000000)
  centralHi := (113836542488537507731/20000000000000000000)
  directionLo := (571367682904622097507/100000000000000000000)
  directionHi := (142841920726155524377/25000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree132.table
  base := (136831291772009737094089677641043941037449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12754632156086049727116485940832602830000000000000)
      constant := (461833134302445669975090909422825775540189501803561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree132.table
  base := (34207822943002425299029657723916651397347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3189501361522214599156961140678047113750000000000)
      constant := (115517100323190873748702155414439761210312101775683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571367682904622097507/100000000000000000000)
  centralHi := (142841920726155524377/25000000000000000000)
  directionLo := (286772164789392714151/50000000000000000000)
  directionHi := (573544329578785428303/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree133.table
  base := (69975447455520312144859653454153211254333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6425604213328685087511900527679860608750000000000)
      constant := (234491749774749073981902707872902704046785309015837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree133.table
  base := (139950894911040595760216079274389368766647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-12854607271887472849607215424374758248750000000000)
      constant := (469222343769513071078879103340255525197294121563383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286772164789392714151/50000000000000000000)
  centralHi := (573544329578785428303/100000000000000000000)
  directionLo := (287856373438282627343/50000000000000000000)
  directionHi := (575712746876565254687/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree134.table
  base := (7155197901906366894865792151142816649883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3236946174307172655732779042471709901250000000000)
      constant := (119047260931013463810606196467141643272994049448935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree134.table
  base := (35775989509531828806275046160987410029511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3237802274421521825646646571509332010625000000000)
      constant := (119107873041200915950149948779314134979153808079879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287856373438282627343/50000000000000000000)
  centralHi := (575712746876565254687/100000000000000000000)
  directionLo := (577873027437984642329/100000000000000000000)
  directionHi := (57787302743798464233/10000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree135.table
  base := (146290481153275209316611857726330152638947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13044360967800011070838431284413957992500000000000)
      constant := (483449766826113458553075229949774168764787463318083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree135.table
  base := (2925809623065503826002979536830994387659/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-6523905461742350877782978573849948918125000000000)
      constant := (241847923239317969970410504954014680897121154906275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577873027437984642329/100000000000000000000)
  centralHi := (57787302743798464233/10000000000000000000)
  directionLo := (145006315544471072129/25000000000000000000)
  directionHi := (580025262177884288517/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree136.table
  base := (18688808032061178946102301516736288106681/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3285234309592832879686436599735269095000000000000)
      constant := (122691417213919401833083942363409544484256606692018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree136.table
  base := (37377616064122354313208074277564113892067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3286103187320829052136332002340616907500000000000)
      constant := (122753851677752637241729691595335763939954700173763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145006315544471072129/25000000000000000000)
  centralHi := (580025262177884288517/100000000000000000000)
  directionLo := (291084770165284094427/50000000000000000000)
  directionHi := (116433908066113637771/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree137.table
  base := (30552781469555012547953766302054329286277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13237513508942651966653061513468194767500000000000)
      constant := (498136749812746934141836038176937131519366431662265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree137.table
  base := (38190976836943762841204521276578088459523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3310253643770482665381174717756259355937500000000)
      constant := (124597543215482030866253418784572536292311540438747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291084770165284094427/50000000000000000000)
  centralHi := (116433908066113637771/20000000000000000000)
  directionLo := (73038243686621839081/12500000000000000000)
  directionHi := (584305949492974712649/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree138.table
  base := (156050810427137029552662152128451936900493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13334089779513972414560376627995313155000000000000)
      constant := (505563009697322055115061752041262092626710898428077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree138.table
  base := (9753175651696063782189399680376693420173/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3334404100220136278626017433171901804375000000000)
      constant := (126455036232847319897016585812240273973850678186388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73038243686621839081/12500000000000000000)
  centralHi := (584305949492974712649/100000000000000000000)
  directionLo := (146608643916608045167/25000000000000000000)
  directionHi := (586434575666432180669/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree139.table
  base := (159371173494580131008575882628955295248587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13430666050085292862467691742522431542500000000000)
      constant := (513044448509403570412635374726590092271851168192043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree139.table
  base := (159371173494580123828369068261111611687973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13434218226679159567483440594350177011250000000000)
      constant := (513305322919394617512184392106509311493219018325797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146608643916608045167/25000000000000000000)
  centralHi := (586434575666432180669/100000000000000000000)
  directionLo := (58855550329705526047/10000000000000000000)
  directionHi := (588555503297055260471/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree140.table
  base := (32544999310021808409519700338463892321579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13527242320656613310375006857049549930000000000000)
      constant := (520581066248992064680175476991496574480938467065655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree140.table
  base := (40681249137527259085842917645139138477593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3382705013119443505115702864003186701250000000000)
      constant := (130211426706486180473824596235195917303626768529977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58855550329705526047/10000000000000000000)
  centralHi := (588555503297055260471/100000000000000000000)
  directionLo := (590668815314835865627/100000000000000000000)
  directionHi := (147667203828708966407/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree141.table
  base := (41528069898432079298731244821124987448163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3405954647806983439570580492894167079375000000000)
      constant := (132043215729022026876068894851323570802078366268707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree141.table
  base := (166112279593728312663503464120710159000113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13627421878276388473442182317675316598750000000000)
      constant := (528441296651040162333790285081315256440842570222257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590668815314835865627/100000000000000000000)
  centralHi := (147667203828708966407/25000000000000000000)
  directionLo := (592774593171479756951/100000000000000000000)
  directionHi := (74096824146434969619/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree142.table
  base := (33906604525088478833048428125791650974519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13720394861799254206189637086103786705000000000000)
      constant := (535819838510692253863266744125461623838573490803955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree142.table
  base := (8476651131272119528283744229686008656443/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3431005926018750731605388294834471598125000000000)
      constant := (134023023098670373453443201904258155350238878188135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592774593171479756951/100000000000000000000)
  centralHi := (74096824146434969619/12500000000000000000)
  directionLo := (11897458337540753753/2000000000000000000)
  directionHi := (594872916877037687651/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree143.table
  base := (172987225645255597405739793931065320731709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13816971132370574654096952200630905092500000000000)
      constant := (543521993032805044570304736052170293669297383636701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree143.table
  base := (172987225645255594546539470659515316228377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13820625529873617379400924041000456186250000000000)
      constant := (543798094056869257154587626302788194585936422419353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11897458337540753753/2000000000000000000)
  centralHi := (594872916877037687651/100000000000000000000)
  directionLo := (298481932517688851241/50000000000000000000)
  directionHi := (596963865035377702483/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree144.table
  base := (176474888653172141563539817819264059389979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13913547402941895102004267315158023480000000000000)
      constant := (551279326482427006707004932647413384143376425460731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree144.table
  base := (176474888653172139292537184943134800133761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-13917227355672231832380294902663025980000000000000)
      constant := (551559301637603979442767218093648478432845282308129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298481932517688851241/50000000000000000000)
  centralHi := (596963865035377702483/100000000000000000000)
  directionLo := (119809502975708617181/20000000000000000000)
  directionHi := (299523757439271542953/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree145.table
  base := (5624875364037379214611597082505354185617/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3502530918378303887477895607421285466875000000000)
      constant := (139772959714889663511594469113878447259480372857704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree145.table
  base := (179996011649196133063848506669889717989349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14013829181470846285359665764325595773750000000000)
      constant := (559375715136886174455230432769305994116344280882661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119809502975708617181/20000000000000000000)
  centralHi := (299523757439271542953/50000000000000000000)
  directionLo := (601123942300038449183/100000000000000000000)
  directionHi := (18785123196876201537/3125000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree146.table
  base := (22943824329166447802274399901915076377619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3526674986021133999454724386053065063750000000000)
      constant := (141739882541050121866057043809186536471830756353382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree146.table
  base := (45887648658332895246418382913360329361337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3527607751817365184584759156497041391875000000000)
      constant := (141811833638679085767722043833742064121667689076793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601123942300038449183/100000000000000000000)
  centralHi := (18785123196876201537/3125000000000000000)
  directionLo := (37699576367942784053/6250000000000000000)
  directionHi := (603193221887084544849/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree147.table
  base := (93569318802791194690205907231748076118359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7101638107327928222863106329369689321250000000000)
      constant := (287441200198176497669247577262118623474454455058551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree147.table
  base := (187138637605582388242752366353480599188091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14207032833068075191318407487650735361250000000000)
      constant := (575174159891094973670148494102289821187556162845499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37699576367942784053/6250000000000000000)
  centralHi := (603193221887084544849/100000000000000000000)
  directionLo := (605255426951880592933/100000000000000000000)
  directionHi := (302627713475940296467/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree148.table
  base := (190760140565952364078407826221068185804301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14299852485227176893633527773266497030000000000000)
      constant := (582860449556016653936255571100471022578342937062189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree148.table
  base := (190760140565952363174959623784907917763783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14303634658866689644297778349313305155000000000000)
      constant := (583156191146022542522050046498986875944467724686887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605255426951880592933/100000000000000000000)
  centralHi := (302627713475940296467/50000000000000000000)
  directionLo := (607310629561911191253/100000000000000000000)
  directionHi := (303655314780955595627/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree149.table
  base := (24301887939305652623835667340502402287161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3599107188949624335385210721948403854375000000000)
      constant := (147723419410797981947073199901656045115164259341458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree149.table
  base := (194415103514445220273263800380159237384153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14400236484665304097277149210975874948750000000000)
      constant := (591193428319499514158935247803998185466946558377817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607310629561911191253/100000000000000000000)
  centralHi := (303655314780955595627/50000000000000000000)
  directionLo := (304679450284666628261/50000000000000000000)
  directionHi := (609358900569333256523/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree150.table
  base := (39620705290212916729223031297691202383163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14493005026369817789448158002320733805000000000000)
      constant := (598982084657879270051275799602499924546044734918535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree150.table
  base := (4952588161276614576911041938265058854563/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3624209577615979637564130018159611185625000000000)
      constant := (149821467852881585434677973495798228837620428483070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304679450284666628261/50000000000000000000)
  centralHi := (609358900569333256523/100000000000000000000)
  directionLo := (152850077409869224819/25000000000000000000)
  directionHi := (611400309639476899277/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree151.table
  base := (5045635234395349685552257566041598511231/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3647395324235284559338868279211963048125000000000)
      constant := (151781417650019780714423691178140436409444283709590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree151.table
  base := (100912704687906993484878642540071199409141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7296720068131266501617945467150507268125000000000)
      constant := (303716760211051733697427261369465295499907869138949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152850077409869224819/25000000000000000000)
  centralHi := (611400309639476899277/100000000000000000000)
  directionLo := (613434925278492668821/100000000000000000000)
  directionHi := (306717462639246334411/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree152.table
  base := (205580752288696882246562638294008733890129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14686157567512458685262788231374970580000000000000)
      constant := (615324435469791917653776441503870954531836514884081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree152.table
  base := (102790376144348440943708113703690054458941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7345020981030573728107630897981792165000000000000)
      constant := (307818187675615661287185985287867591598767332941149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613434925278492668821/100000000000000000000)
  centralHi := (306717462639246334411/50000000000000000000)
  directionLo := (123092562972035242087/20000000000000000000)
  directionHi := (153865703715044052609/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree153.table
  base := (209369555189716635206183054171526139510299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14782733838083779133170103345902088967500000000000)
      constant := (623578379267018075525656809092020420777769453177211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree153.table
  base := (52342388797429158730259478521626826183229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3696660946964940477298658164406538530937500000000)
      constant := (155973609049727582091005394259359207143070735984981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123092562972035242087/20000000000000000000)
  centralHi := (153865703715044052609/25000000000000000000)
  directionLo := (617484044652000051677/100000000000000000000)
  directionHi := (308742022326000025839/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree154.table
  base := (106595909039438266531535312099906963759787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7439655054327549790538709230214603677500000000000)
      constant := (315943750995879003757063471709649312768777980968843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree154.table
  base := (21319181807887653283668863866611613284937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7441622806829188181087001759644361958750000000000)
      constant := (316103851482570447902544027667673228822758538085965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617484044652000051677/100000000000000000000)
  centralHi := (308742022326000025839/50000000000000000000)
  directionLo := (309749339920190487111/50000000000000000000)
  directionHi := (619498679840380974223/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree155.table
  base := (108523770478089892341469367237160868908441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7487943189613210014492366787478162871250000000000)
      constant := (320125901822006057459146615085631103001094994246649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree155.table
  base := (217047540956179784503217479388458433075359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-14979847439456990815153374380951293711250000000000)
      constant := (640576175649923426197069939212561103712949782531551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309749339920190487111/50000000000000000000)
  centralHi := (619498679840380974223/100000000000000000000)
  directionLo := (38844174034700639277/6250000000000000000)
  directionHi := (621506784555210228433/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree156.table
  base := (110468361910814761688715110700321879194263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7536231324898870238446024344741722065000000000000)
      constant := (324335642111890394794254300109652684031304262511607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree156.table
  base := (44187344764325904646951631486299335216321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15076449265255605268132745242613863505000000000000)
      constant := (648999854253258311390631668317265231417839043599845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38844174034700639277/6250000000000000000)
  centralHi := (621506784555210228433/100000000000000000000)
  directionLo := (62350842189367270663/10000000000000000000)
  directionHi := (623508421893672706631/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree157.table
  base := (224859366675228809163577527967390635744033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15169038920369060924799363804010562517500000000000)
      constant := (657145943731064414208939462180005391991252651779137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree157.table
  base := (112429683337614404525160844799178311549113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7586525545527109860556058052138216649375000000000)
      constant := (328739369387572967035093545348114081031179713933257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62350842189367270663/10000000000000000000)
  centralHi := (623508421893672706631/100000000000000000000)
  directionLo := (312751826971690052293/50000000000000000000)
  directionHi := (625503653943380104587/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree158.table
  base := (228815469516980630943322338929337328436589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15265615190940381372706678918537680905000000000000)
      constant := (665675782165863362570135314256593524414779989243021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree158.table
  base := (228815469516980630853421315619975952602057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15269652916852834174091486965939003092500000000000)
      constant := (666012829215586668026482242414935459207670218768873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312751826971690052293/50000000000000000000)
  centralHi := (625503653943380104587/100000000000000000000)
  directionLo := (627492541804842066063/100000000000000000000)
  directionHi := (39218283862802629129/6250000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree159.table
  base := (232805032346887908606013427145711221176331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6054856)
      previous := (3027428)
      next := (3027428)
      square := (32556395224362688022717860107150000000000000)
      linear := (-5468918284625027348029189759012032500000000000)
      constant := (240035884488493413966524047890929800996741432451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree159.table
  base := (5820125808672197713366350332308547780051/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (8139098806090672005679465026787500000000000)
      linear := (-1367591201731172003121293861481094062500000000)
      constant := (60039349018741623212846486064569031164578380710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627492541804842066063/100000000000000000000)
  centralHi := (39218283862802629129/6250000000000000000)
  directionLo := (629475145613298319671/100000000000000000000)
  directionHi := (78684393201662289959/12500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree160.table
  base := (23682805516495349505676037827696916212633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7729383866041511134260654573795958840000000000000)
      constant := (341450497909004341388643420629394356342138491622685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree160.table
  base := (236828055164953495000120705695519256713723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15462856568450063080050228689264142680000000000000)
      constant := (683246627852128922032348862138735891634278017667547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629475145613298319671/100000000000000000000)
  centralHi := (78684393201662289959/12500000000000000000)
  directionLo := (631451524559933878099/100000000000000000000)
  directionHi := (6314515245599338781/1000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree161.table
  base := (240884537971180178173461339382723249025603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15555344002654342716428624262119036067500000000000)
      constant := (691596371035355760056683023121416170949530409096867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree161.table
  base := (30110567246397522266063354175122839152779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3889864598562169383257399887731678118437500000000)
      constant := (172986584012057786878895817939064682146349516214862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631451524559933878099/100000000000000000000)
  centralHi := (6314515245599338781/1000000000000000000)
  directionLo := (158355434228124618633/25000000000000000000)
  directionHi := (633421736912498474533/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree162.table
  base := (244974480765570682695250294637166287868551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15651920273225663164335939376646154455000000000000)
      constant := (700346925180219572424638350476862825100742887230439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree162.table
  base := (244974480765570682659571598897971281215397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15656060220047291986008970412589282267500000000000)
      constant := (700701250162887895623808290120417902418441597752133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158355434228124618633/25000000000000000000)
  centralHi := (633421736912498474533/100000000000000000000)
  directionLo := (127077168007070111503/20000000000000000000)
  directionHi := (158846460008837639379/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree163.table
  base := (249097883548127672045027732643440197969779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15748496543796983612243254491173272842500000000000)
      constant := (709152658252600452967459749327687927361878149182931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree163.table
  base := (6227447088703191800417799414669844734531/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-3938165511461476609747085318562963015312500000000)
      constant := (177377842549024874860848233373465529172830297021590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127077168007070111503/20000000000000000000)
  centralHi := (158846460008837639379/25000000000000000000)
  directionLo := (79667986301118168919/12500000000000000000)
  directionHi := (637343890408945351353/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree164.table
  base := (126627373159426875044325555052811389065111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7922536407184152030075284802850195615000000000000)
      constant := (359006785126249363661640388878071535733612969388279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree164.table
  base := (50650949263770750013235932936655111586249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-15849263871644520891967712135914421855000000000000)
      constant := (718376696147866284612520063600844697662946396833805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79667986301118168919/12500000000000000000)
  centralHi := (637343890408945351353/100000000000000000000)
  directionLo := (159823985912196428107/25000000000000000000)
  directionHi := (639295943648785712429/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree165.table
  base := (128722534538875731416635332258377717674109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7970824542469812254028942360113754808750000000000)
      constant := (363464830589957356947227317404668328415919715070301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree165.table
  base := (128722534538875731407718969866114383824307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-7972932848721567672473541498788495824375000000000)
      constant := (363648614009094284766791013996162771131520042949123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159823985912196428107/25000000000000000000)
  centralHi := (639295943648785712429/100000000000000000000)
  directionLo := (80155256815481721321/12500000000000000000)
  directionHi := (641242054523853770569/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree166.table
  base := (261668851824823300067203732825066492692163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-16038225355510944955965199834754628005000000000000)
      constant := (735900931034848724052636004815854936993979139084707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree166.table
  base := (10466754072992932002122107588968959618917/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-16042467523241749797926453859239561442500000000000)
      constant := (736272965807066665578264594663236643036803618835325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80155256815481721321/12500000000000000000)
  centralHi := (641242054523853770569/100000000000000000000)
  directionLo := (643182276974540636949/100000000000000000000)
  directionHi := (12863645539490812739/2000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree167.table
  base := (265926094560071696943648185208192877007621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-16134801626082265403872514949281746392500000000000)
      constant := (744927379817301062336839450136001525252481681365669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree167.table
  base := (265926094560071696932419124240111991004139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-16139069349040364250905824720902131236250000000000)
      constant := (745303909514500877285607005138807100790367407724971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643182276974540636949/100000000000000000000)
  centralHi := (12863645539490812739/2000000000000000000)
  directionLo := (645116664130090784361/100000000000000000000)
  directionHi := (322558332065045392181/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree168.table
  base := (270216797283499035510443921222847076992317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91450914185234790655814469040984350000000000000)
      linear := (-16231377896653585851779830063808864780000000000000)
      constant := (754009007527272026644750602162150211963802820946013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree168.table
  base := (135108398641749517750766907786807080773681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-8117835587419489351942597791282350515000000000000)
      constant := (377195029570245751276657242111920635376888270509009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell142.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645116664130090784361/100000000000000000000)
  centralHi := (322558332065045392181/50000000000000000000)
  directionLo := (323522634162788530129/50000000000000000000)
  directionHi := (647045268325577060259/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree169.table
  base := (68635239998776911547000340111202571965993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22862728546308697663953617260246087500000000000)
      linear := (-4081988541806226574921786294583995791875000000000)
      constant := (190786453541190477104388785784180947544419997457577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree169.table
  base := (137270479997553823090465782242704400777809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45725457092617395327907234520492175000000000000)
      linear := (-8166136500318796578432283222113635411875000000000)
      constant := (381765707342519416411294134604093196175007589829601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell142.Kernel169
