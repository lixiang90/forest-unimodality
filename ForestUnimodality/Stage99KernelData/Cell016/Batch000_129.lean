import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell016.Parameters
import ForestUnimodality.BinomialMassData.Q19_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_51.Batch100_149
import ForestUnimodality.BinomialMassData.Q97_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q97_255.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree000.table
  base := (1130817142007559160775898021/100000000000000000000000000)
  polynomial :=
    { denominator := 17000000000000000000000000000000000000000
      center := (32)
      previous := (19)
      next := (0)
      square := (481525043528290425109972262000000000000)
      linear := (1279730815186471429290016028000000000000)
      constant := (192238914141285057331902663570000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree000.table
  base := (1130817142007559160775898021/100000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (158)
      previous := (97)
      next := (0)
      square := (2407625217641452125549861310000000000000)
      linear := (6398654075932357146450080140000000000000)
      constant := (961194570706425286659513317850000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree001.table
  base := (74058367010025242752345849027616224529027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (1409049597613050202188356144160000000000000)
      constant := (191998619287662728180311950059329799999999227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree001.table
  base := (73242037918885525117423927623098577470203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (1397492996568371231985716809872000000000000)
      constant := (189864341272219375861157781219692999999998003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12087086280331326373/25000000000000000000)
  directionHi := (48348345121325305493/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree002.table
  base := (49005279303353547704736152055014480215301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (860111047990799117562987765480000000000000)
      constant := (126412851375683442135250936721012663039997901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree002.table
  base := (47967283923918135376759143051665140976547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (836997845901441177157709096904000000000000)
      constant := (123699714735780622981596691622027431679998747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/25000000000000000000)
  centralHi := (48348345121325305493/100000000000000000000)
  directionLo := (68374885388873310623/100000000000000000000)
  directionHi := (2136715168402290957/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree003.table
  base := (16397092184115363730686901655875967746637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (17287361020474890718756632600000000000000)
      constant := (4668311843388305580463815993118154678778093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree003.table
  base := (15898490638916831243306100699099744657181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (15361260846361729018316743552000000000000)
      constant := (4523831895392202201966798947478626205925309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68374885388873310623/100000000000000000000)
  centralHi := (2136715168402290957/3125000000000000000)
  directionLo := (41870895106005142003/50000000000000000000)
  directionHi := (83741790212010284007/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree004.table
  base := (11092388875331619340738966832198195317917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-118883025626851525843874495940000000000000)
      constant := (28210436409371848445117081454307506021902117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree004.table
  base := (21324725872971031867006714962295469140759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-283992455432418932498306329032000000000000)
      constant := (54192062332029970840056265108700115235114159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41870895106005142003/50000000000000000000)
  centralHi := (83741790212010284007/100000000000000000000)
  directionLo := (12087086280331326373/12500000000000000000)
  directionHi := (19339338048530122197/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree005.table
  base := (1512560631974927007341979660966882447241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-78670460087595413631311737056000000000000)
      constant := (3825080069547042029138099216344861245273841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree005.table
  base := (2884208422653512870749670922858498108953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-844487606099348987326314042000000000000000)
      constant := (36450213355332588089488893718034767906933765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/12500000000000000000)
  centralHi := (19339338048530122197/20000000000000000000)
  directionLo := (5405509314545185007/5000000000000000000)
  directionHi := (108110186290903700141/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree006.table
  base := (1033352141726662917136597990437773708767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (544)
      previous := (323)
      next := (0)
      square := (8185925739980937226869528454000000000000)
      linear := (-14840479449980058010427619436000000000000)
      constant := (290910301679263867201738559956516601833663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree006.table
  base := (4885009541889673318693339821084202678043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-78054597598126613453017875276000000000000)
      constant := (1376707938733242936989981699480534573954427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5405509314545185007/5000000000000000000)
  centralHi := (108110186290903700141/100000000000000000000)
  directionLo := (118428775455227446231/100000000000000000000)
  directionHi := (14803596931903430779/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree007.table
  base := (6998391725711404047117297340997823040363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-1884581700120456305563854127920000000000000)
      constant := (18107100628906005235314514280755337727984163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree007.table
  base := (6550965798659140513335233091484841727789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-1965477907433209096982329467936000000000000)
      constant := (17049033703438658598919221188050473333979189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118428775455227446231/100000000000000000000)
  centralHi := (14803596931903430779/12500000000000000000)
  directionLo := (15989712186568716153/12500000000000000000)
  directionHi := (5116707899701989169/4000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree008.table
  base := (4607929972900133783147334032805642896977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-2433520249742707390189222506600000000000000)
      constant := (12693861933838010006368918697087477175037177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree008.table
  base := (850226215650822086348876229775599757321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-2525973058100139151810337180904000000000000)
      constant := (11921419955776420023628647961678074843959605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15989712186568716153/12500000000000000000)
  centralHi := (5116707899701989169/4000000000000000000)
  directionLo := (68374885388873310623/50000000000000000000)
  directionHi := (136749770777746621247/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree009.table
  base := (567467020357226535074608062138236624947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1088)
      previous := (646)
      next := (0)
      square := (16371851479961874453739056908000000000000)
      linear := (-66276862208110188329213130784000000000000)
      constant := (202164522590029618777770476793950384609683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree009.table
  base := (2549212430944137029141848005718165874597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-342940912085229911848704988208000000000000)
      constant := (951354874834191852839617948142949937758533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68374885388873310623/50000000000000000000)
  centralHi := (136749770777746621247/100000000000000000000)
  directionLo := (36261258840993979119/25000000000000000000)
  directionHi := (145045035363975916477/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree010.table
  base := (369973544238088883872325426053815383071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-1765698674493604779719979631980000000000000)
      constant := (3390032516013119608212584909531947622735342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree010.table
  base := (248603236614956257847436688000869182823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-3646963359433999261466352606840000000000000)
      constant := (6445449711457382673331500875451303722613115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36261258840993979119/25000000000000000000)
  centralHi := (145045035363975916477/100000000000000000000)
  directionLo := (30578178336655573041/20000000000000000000)
  directionHi := (76445445841638932603/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree011.table
  base := (403353389746061981203549803244000121321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-4080335898609460644065327642640000000000000)
      constant := (5397854323956951386302443352337644315555921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree011.table
  base := (102272054474983453137744932594039660527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-2103729255050464658147180159904000000000000)
      constant := (2619132042294946772842488682779897157030727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30578178336655573041/20000000000000000000)
  centralHi := (76445445841638932603/50000000000000000000)
  directionLo := (16035332000204606041/10000000000000000000)
  directionHi := (160353320002046060411/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree012.table
  base := (-477514948670112612116477336011795286773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-514363827581301303187855113480000000000000)
      constant := (525454908186387107329219859972591162122603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree012.table
  base := (-647897966084056103774540124412386457881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-529772628974206596791374225864000000000000)
      constant := (525350049403428398239062271270420313672391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16035332000204606041/10000000000000000000)
  centralHi := (160353320002046060411/100000000000000000000)
  directionLo := (41870895106005142003/25000000000000000000)
  directionHi := (167483580424020568013/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree013.table
  base := (-1218168846407016218610180698834392530139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-5178212997853962813316064400000000000000000)
      constant := (4629538302091521374670194018591745029108461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree013.table
  base := (-1367029337046779333407539311378059884097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-5328448811434789425950375745744000000000000)
      constant := (4777985905234571156652710235580066241463703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41870895106005142003/25000000000000000000)
  centralHi := (167483580424020568013/100000000000000000000)
  directionLo := (174322437418767599383/100000000000000000000)
  directionHi := (21790304677345949923/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree014.table
  base := (-1855158832958137750167722151123718162691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-5727151547476213897941432778680000000000000)
      constant := (5004118781986498952597778175647209058840709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree014.table
  base := (-1987369534844372674183399787947413967749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-5888943962101719480778383458712000000000000)
      constant := (5297985166514092375241147416086376269884851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174322437418767599383/100000000000000000000)
  centralHi := (21790304677345949923/12500000000000000000)
  directionLo := (180902942661502680617/100000000000000000000)
  directionHi := (90451471330751340309/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree015.table
  base := (-2412971981586864456820387696191475964659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-697343344122051664729644573040000000000000)
      constant := (643238303978260718046039590700663446213549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree015.table
  base := (-316493233345000257387861592668186686557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-358302172931591640867021731760000000000000)
      constant := (346014122345883591565659229165576190340108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180902942661502680617/100000000000000000000)
  centralHi := (90451471330751340309/50000000000000000000)
  directionLo := (1462908870871730631/781250000000000000)
  directionHi := (187252335471581520769/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree016.table
  base := (-2908350263100735506070724395338825525929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-6825028646720716067192169536040000000000000)
      constant := (6941070297474654529445803534123714807058671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree016.table
  base := (-3016475786695013540579905411726227828787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-7009934263435579590434398884648000000000000)
      constant := (7527911914772606893146345650621681417325013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1462908870871730631/781250000000000000)
  centralHi := (187252335471581520769/100000000000000000000)
  directionLo := (12087086280331326373/6250000000000000000)
  directionHi := (193393380485301221969/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree017.table
  base := (-134120829855489483363794194981889732313/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (576)
      previous := (342)
      next := (0)
      square := (8667450783509227651979500716000000000000)
      linear := (-86752555251093731197853387232000000000000)
      constant := (99169333656718489217035586810854354780555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree017.table
  base := (-1725990448599824014030715025000064249671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1422)
      previous := (873)
      next := (0)
      square := (21668626958773069129948751790000000000000)
      linear := (-222659688650073813095953135224000000000000)
      constant := (269655621056500661901851739658590169800337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/6250000000000000000)
  centralHi := (193393380485301221969/100000000000000000000)
  directionLo := (4983633343976013499/2500000000000000000)
  directionHi := (199345333759040539961/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree018.table
  base := (-938856645258547600877273873173116672023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-440161430331401013135717016300000000000000)
      constant := (568452960764759702800332305625938563570706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree018.table
  base := (-3846426172955063781072209041387417575067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-903436062752159966676712701176000000000000)
      constant := (1236519434058384316634205741592636320805637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4983633343976013499/2500000000000000000)
  centralHi := (199345333759040539961/100000000000000000000)
  directionLo := (205124656166619931869/100000000000000000000)
  directionHi := (20512465616661993187/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree019.table
  base := (-824365754642052913794101475547301221681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-1694368859117493864213654934416000000000000)
      constant := (2466613043852751077821331481465469522407719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree019.table
  base := (-105143818129625527118707034047930113891/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-4345709857718184877459211011776000000000000)
      constant := (6696805228146457713321092925897475475390180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205124656166619931869/100000000000000000000)
  centralHi := (20512465616661993187/10000000000000000000)
  directionLo := (21074555047128475237/10000000000000000000)
  directionHi := (210745550471284752371/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree020.table
  base := (-4457011273123200102513030783435657003037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-9020782845209720405693643050760000000000000)
      constant := (14719686082824980701739773997083856135100763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree020.table
  base := (-4534532709435003023198888217906634505203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-9251914866103299809746429736520000000000000)
      constant := (15951205588649590733697825303144843651966997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21074555047128475237/10000000000000000000)
  centralHi := (210745550471284752371/100000000000000000000)
  directionLo := (216220372581807400281/100000000000000000000)
  directionHi := (108110186290903700141/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree021.table
  base := (-952947107880728264043387314099004830227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1088)
      previous := (646)
      next := (0)
      square := (16371851479961874453739056908000000000000)
      linear := (-212660475440710477562644698432000000000000)
      constant := (386271829567800993826234372485387604064397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree021.table
  base := (-1209097080014798065164348570665529812557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-545133889820568325809690969416000000000000)
      constant := (1044002165337791981177988250728523768342054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216220372581807400281/100000000000000000000)
  centralHi := (108110186290903700141/50000000000000000000)
  directionLo := (110779975622161054267/50000000000000000000)
  directionHi := (44311990248864421707/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree022.table
  base := (-5048036507920887598965343950600414074693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-10118659944454222574944379808120000000000000)
      constant := (20312810094245899771155982632008322991723507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree022.table
  base := (-5114263059876385224423415718202714855487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-10372905167437159919402445162456000000000000)
      constant := (21908454567753220701753773844289138660878313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110779975622161054267/50000000000000000000)
  centralHi := (44311990248864421707/20000000000000000000)
  directionLo := (226773839918446436133/100000000000000000000)
  directionHi := (113386919959223218067/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree023.table
  base := (-1327354455525579376738691618310847769813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-5333799247038236829784874093400000000000000)
      constant := (11752453698677467096393474932676969901432774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree023.table
  base := (-268530006206768882364845405637929164057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-5466700159052044987115226437712000000000000)
      constant := (12647048806413184077167548405842662442877430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226773839918446436133/100000000000000000000)
  centralHi := (113386919959223218067/50000000000000000000)
  directionLo := (11593525881642731597/5000000000000000000)
  directionHi := (231870517632854631941/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree024.table
  base := (-5550982775945795244341068841894491426553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-1246281893744302749355012951720000000000000)
      constant := (2994783730243300355829782707572491977726183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree024.table
  base := (-2803731021637380006908037421111992902007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-638549748265056668281025588244000000000000)
      constant := (1607977970534940231592438357477834051319977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11593525881642731597/5000000000000000000)
  centralHi := (231870517632854631941/100000000000000000000)
  directionLo := (118428775455227446231/50000000000000000000)
  directionHi := (236857550910454892463/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree025.table
  base := (-721815496023014511376085165466230753119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-5882737796660487914410242472080000000000000)
      constant := (15326293034723103138609931507739335244549924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree025.table
  base := (-5826612882502534404130995345189014638717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-12054390619437950083886468301360000000000000)
      constant := (32852383804554875334269798093263372924697083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118428775455227446231/50000000000000000000)
  centralHi := (236857550910454892463/100000000000000000000)
  directionLo := (12087086280331326373/5000000000000000000)
  directionHi := (241741725606626527461/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree026.table
  base := (-149539655201438354396099824815651822273/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-1231441414294322691344585332284000000000000)
      constant := (3459948684029054242780890782617958441071708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree026.table
  base := (-6029576317441367419189835354602939235181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-12614885770104880138714476014328000000000000)
      constant := (37016475537309665822086640716271355049294219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/5000000000000000000)
  centralHi := (241741725606626527461/100000000000000000000)
  directionLo := (24652915522355625067/10000000000000000000)
  directionHi := (246529155223556250671/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree027.table
  base := (-6173511892225978423964783460720826907509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-1429261410285053110896802411280000000000000)
      constant := (4310029367890026280000426003231681023729899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree027.table
  base := (-1554419486441784441274594487930023078681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-731965606709545010752360207072000000000000)
      constant := (2301801710463240839862959806071246660522382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24652915522355625067/10000000000000000000)
  centralHi := (246529155223556250671/100000000000000000000)
  directionLo := (251225370636030852019/100000000000000000000)
  directionHi := (12561268531801542601/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree028.table
  base := (-3175737361029512893145354244878553715823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-6706145621093864541348295040100000000000000)
      constant := (21610932842171509452231308493950881785144377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree028.table
  base := (-3196038554411007003282011841041339336359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-6867938035719370124185245720132000000000000)
      constant := (23048617055404951391902878326670676386130241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251225370636030852019/100000000000000000000)
  centralHi := (12561268531801542601/5000000000000000000)
  directionLo := (255835394985099458449/100000000000000000000)
  directionHi := (5116707899701989169/2000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree029.table
  base := (-6516505518436354688601528290715487946377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-13961229791809980167321958458880000000000000)
      constant := (47891609795180845995732100393869015851473423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree029.table
  base := (-6553791573891245479383480375514156807469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-14296371222105670303198499153232000000000000)
      constant := (51008238292015435298496844083077278143773131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255835394985099458449/100000000000000000000)
  centralHi := (5116707899701989169/2000000000000000000)
  directionLo := (130181903315277113829/50000000000000000000)
  directionHi := (260363806630554227659/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree030.table
  base := (-833689069666976200430291434318696798553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-806120463412901736219295935420000000000000)
      constant := (2933174123205852462262361598327586500872732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree030.table
  base := (-837964653304454690217296115083074279267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-825381465154033353223694825900000000000000)
      constant := (3120172951881743220944230159283966133167348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130181903315277113829/50000000000000000000)
  centralHi := (260363806630554227659/100000000000000000000)
  directionLo := (264814792409947171499/100000000000000000000)
  directionHi := (529629584819894343/200000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree031.table
  base := (-1362259601007912966873288715436070779669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-3011821378210896467314539043248000000000000)
      constant := (11587270503483315703178328479410779902080931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree031.table
  base := (-6842644168698471806885671021749389607383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-15417361523439530412854514579168000000000000)
      constant := (61559803580442955187162243592779437631196817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264814792409947171499/100000000000000000000)
  centralHi := (529629584819894343/200000000000000000)
  directionLo := (67298048242080447119/25000000000000000000)
  directionHi := (269192192968321788477/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree032.table
  base := (-3471285747668462625473602542007370667457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-7804022720338366710599031797460000000000000)
      constant := (31653709468414283307739621336398828893944343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree032.table
  base := (-6971270147175939337154626396778426863803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-15977856674106460467682522292136000000000000)
      constant := (67196494793093574131936793753537711727248397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67298048242080447119/25000000000000000000)
  centralHi := (269192192968321788477/100000000000000000000)
  directionLo := (273499541555493242493/100000000000000000000)
  directionHi := (136749770777746621247/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree033.table
  base := (-353198077434045822055212258171432851957/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (544)
      previous := (323)
      next := (0)
      square := (8185925739980937226869528454000000000000)
      linear := (-179522044336655383398038133040000000000000)
      constant := (765652207713810989614515045890911811568854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree033.table
  base := (-1418042386246122606297608291359942191431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-1837594647197043391390058889456000000000000)
      constant := (8119064728301242516572172652694483533382205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273499541555493242493/100000000000000000000)
  centralHi := (136749770777746621247/50000000000000000000)
  directionLo := (69435024351473620819/25000000000000000000)
  directionHi := (277740097405894483277/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree034.table
  base := (-717602531325215757769717730403846252337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 153000000000000000000000000000000000000000
      center := (288)
      previous := (171)
      next := (0)
      square := (4333725391754613825989750358000000000000)
      linear := (-98270132587771974061463531484000000000000)
      constant := (439639662630835619980971306384211523392439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree034.table
  base := (-3600007536661205635887108604190555641727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1422)
      previous := (873)
      next := (0)
      square := (21668626958773069129948751790000000000000)
      linear := (-502907263983538840509956991708000000000000)
      constant := (2328930820098456853750266265789244986815769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69435024351473620819/25000000000000000000)
  centralHi := (277740097405894483277/100000000000000000000)
  directionLo := (140958437298913164373/50000000000000000000)
  directionHi := (281916874597826328747/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree035.table
  base := (-7279256965278264107646753038656873365293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-17254861089543486675074168730960000000000000)
      constant := (80796265443457737832414671801353472376872907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree035.table
  base := (-7301162357363949995826564248490903324643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-17659342126107250632166545431040000000000000)
      constant := (85531435058045911212762610278575160452603557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140958437298913164373/50000000000000000000)
  centralHi := (281916874597826328747/100000000000000000000)
  directionLo := (143016333559297796397/50000000000000000000)
  directionHi := (57206533423719118559/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree036.table
  base := (-1843523753107837363833240693871980953953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-989099979953652097761085394980000000000000)
      constant := (4837784806913048297524591568141995008615166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree036.table
  base := (-739408116036028741049795243118067851459/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1012213182043010038166364063556000000000000)
      constant := (5117435137289786711604772839393591954641745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143016333559297796397/50000000000000000000)
  centralHi := (57206533423719118559/20000000000000000000)
  directionLo := (36261258840993979119/12500000000000000000)
  directionHi := (290090070727951832953/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree037.table
  base := (-233154021307832164504785498659040912843/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-9176369094393994422162452744160000000000000)
      constant := (46794656755192175038686298740415353371125712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree037.table
  base := (-7479149898072743286352765604871749201479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-18780332427441110741822560856976000000000000)
      constant := (98929855863463089092640993138618980326953121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36261258840993979119/12500000000000000000)
  centralHi := (290090070727951832953/100000000000000000000)
  directionLo := (147045751052962150317/50000000000000000000)
  directionHi := (58818300421184860127/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree038.table
  base := (-3770051766036041852694282256540889227501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-9450838369205119964475136933500000000000000)
      constant := (50161463801777047786350939627617147119269899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree038.table
  base := (-3778351844084135010205368007890725581303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-9670413789054020398325284284972000000000000)
      constant := (52989316796867476439689766397383422763030897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147045751052962150317/50000000000000000000)
  centralHi := (58818300421184860127/20000000000000000000)
  directionLo := (298039215686274509803/100000000000000000000)
  directionHi := (74509803921568627451/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree039.table
  base := (-1522385279758901279492697081262695476851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1088)
      previous := (646)
      next := (0)
      square := (16371851479961874453739056908000000000000)
      linear := (-432235895289610911412792049904000000000000)
      constant := (2384003793873145414220201182431081007190061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree039.table
  base := (-7627039338064523637294161749917168820461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-2211258080974996761275397364768000000000000)
      constant := (12584377073993158761006548083980338210886771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298039215686274509803/100000000000000000000)
  centralHi := (74509803921568627451/25000000000000000000)
  directionLo := (301935318508551493857/100000000000000000000)
  directionHi := (150967659254275746929/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree040.table
  base := (-1919167440869277166413344395339556038669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-9999776918827371049100505312180000000000000)
      constant := (57230167074160642810976299304243629486843862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree040.table
  base := (-480651234101306756613593719021645040203/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-10230908939720950453153291997940000000000000)
      constant := (60385726141370603639396395576357610003455976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301935318508551493857/100000000000000000000)
  centralHi := (150967659254275746929/50000000000000000000)
  directionLo := (30578178336655573041/10000000000000000000)
  directionHi := (305781783366555730411/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree041.table
  base := (-3867287809196448709408131315862170429227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-10274246193638496591413189501520000000000000)
      constant := (60931394226870615274446400643892494713580573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree041.table
  base := (-3873538893270028915441547389420945714891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-10511156515054415480567295854424000000000000)
      constant := (64257101867220368040715053670266920195568509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30578178336655573041/10000000000000000000)
  centralHi := (305781783366555730411/100000000000000000000)
  directionLo := (309580460486126286837/100000000000000000000)
  directionHi := (154790230243063143419/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree042.table
  base := (-7785858890131328595584819441442226714757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-2344158992988804918605749709080000000000000)
      constant := (14387441624054689280482895941103196479435227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree042.table
  base := (-121831558614038165656183331779885185459/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1199044898931986723109033301212000000000000)
      constant := (7582617303305984296359385212016421804875168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309580460486126286837/100000000000000000000)
  centralHi := (154790230243063143419/50000000000000000000)
  directionLo := (4895829498881906597/1562500000000000000)
  directionHi := (313333087928442022209/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree043.table
  base := (-7830710474481551381006948792354651157509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-21646369486521495352077115760400000000000000)
      constant := (137332396116626627518002795221345552339319091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree043.table
  base := (-7841028385636459365004190454460942951561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-22143303331442691070790607134784000000000000)
      constant := (144689700136271378581756605283669487382989839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4895829498881906597/1562500000000000000)
  centralHi := (313333087928442022209/100000000000000000000)
  directionLo := (9907540652650851373/3125000000000000000)
  directionHi := (317041300884827243937/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree044.table
  base := (-314771997134958855602658176332309364403/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-4439061607228749287340496827816000000000000)
      constant := (29079722387313703505058024611262316715938985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree044.table
  base := (-984833197683786652775767591915734594613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-11351899241054810562809307423876000000000000)
      constant := (76560774341928861186108435450889497277646348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9907540652650851373/3125000000000000000)
  centralHi := (317041300884827243937/100000000000000000000)
  directionLo := (320706640004092120821/100000000000000000000)
  directionHi := (160353320002046060411/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree045.table
  base := (-61732639520422509350131888199247516919/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1263569254764777640073769584320000000000000)
      constant := (8538068352667599297838598632716717927066176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree045.table
  base := (-7910274759119967372143991046864114945637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-2584921514752950131160735840080000000000000)
      constant := (17975809340668263151826770015636270780710907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320706640004092120821/100000000000000000000)
  centralHi := (160353320002046060411/50000000000000000000)
  directionLo := (162165279436355550211/50000000000000000000)
  directionHi := (324330558872711100423/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree046.table
  base := (-991034755272005611929883686722931417343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-11646592567694124302976610448220000000000000)
      constant := (81095951698530818108226195174934621533963428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree046.table
  base := (-7935982976697778106155824677497228057713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-23824788783443481235274630273688000000000000)
      constant := (170671575804591233910658428367327309821888487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162165279436355550211/50000000000000000000)
  centralHi := (324330558872711100423/100000000000000000000)
  directionLo := (81978607687713224839/25000000000000000000)
  directionHi := (327914430750852899357/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree047.table
  base := (-3974459654304207110163530276485391901829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-11921061842505249845289294637560000000000000)
      constant := (85459161004023640515102031396871495663342771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree047.table
  base := (-3977951399086918727161337197083054028169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-12192641967055205645051318993328000000000000)
      constant := (89894565560351028807314299677384176472732431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81978607687713224839/25000000000000000000)
  centralHi := (327914430750852899357/100000000000000000000)
  directionLo := (66291910930558241691/20000000000000000000)
  directionHi := (41432444331598901057/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree048.table
  base := (-7963807211483402441380051176043693141249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-2710118026070305641689328628200000000000000)
      constant := (19984912404014710565260220346763372682179039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree048.table
  base := (-7970133947892414550395909444022734525863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-2771753231641926816103405077736000000000000)
      constant := (21014965625703043940162681299023029722025593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66291910930558241691/20000000000000000000)
  centralHi := (41432444331598901057/12500000000000000000)
  directionLo := (13398686433921645441/4000000000000000000)
  directionHi := (167483580424020568013/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree049.table
  base := (-7973035512682021701550984442291325648709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-24940000784255001859829326032480000000000000)
      constant := (189029328406664465804045546382020261987707891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree049.table
  base := (-3989382388026460177889191689971448112827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-12753137117722135699879326706296000000000000)
      constant := (99354012268799289770278101642807063458536973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13398686433921645441/4000000000000000000)
  centralHi := (167483580424020568013/50000000000000000000)
  directionLo := (67687683169855427689/20000000000000000000)
  directionHi := (169219207924638569223/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree050.table
  base := (-3988343750283725486703610677182773979407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-12744469666938626472227347205580000000000000)
      constant := (99206727843305432336333523304647604879562393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree050.table
  base := (-7981873556816187370884480197394559152399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-26066769386111201454586661125560000000000000)
      constant := (208508929248423284518327001365776751644610201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67687683169855427689/20000000000000000000)
  centralHi := (169219207924638569223/50000000000000000000)
  directionLo := (85468606736091638279/25000000000000000000)
  directionHi := (341874426944366553117/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree051.table
  base := (-7974837160695574876881027230730994123947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (320)
      previous := (190)
      next := (0)
      square := (4815250435282904251099722620000000000000)
      linear := (-170182208388885647248889299280000000000000)
      constant := (1359584320519874090174919357577573099892901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree051.table
  base := (-7979529638190512809532493525364721137951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (316)
      previous := (194)
      next := (0)
      square := (4815250435282904251099722620000000000000)
      linear := (-174034408737111970649769077376000000000000)
      constant := (1428347871827659668899576105899999740654833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85468606736091638279/25000000000000000000)
  centralHi := (341874426944366553117/100000000000000000000)
  directionLo := (345276246322433544729/100000000000000000000)
  directionHi := (34527624632243354473/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree052.table
  base := (-1991887553898947174019136881446157573757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-13293408216560877556852715584260000000000000)
      constant := (108918996760577561021188754677677088301316086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree052.table
  base := (-7971794460644971551570908108149026928889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-27187759687445061564242676551496000000000000)
      constant := (228792750154564450247994722976470780957959711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345276246322433544729/100000000000000000000)
  centralHi := (34527624632243354473/10000000000000000000)
  directionLo := (174322437418767599383/50000000000000000000)
  directionHi := (348644874837535198767/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree053.table
  base := (-3977442524143832924616579744379505694551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-13567877491372003099165399773600000000000000)
      constant := (113939040638610056474335484660998905688472849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree053.table
  base := (-7958722459450553505304029683708006253151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-27748254838111991619070684264464000000000000)
      constant := (239275364957081002485906238462653875735554249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174322437418767599383/50000000000000000000)
  centralHi := (348644874837535198767/100000000000000000000)
  directionLo := (351981265448107855483/100000000000000000000)
  directionHi := (87995316362026963871/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree054.table
  base := (-3968446761273864472509251613108751571311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1538038529575903182386453773660000000000000)
      constant := (13229807189447387400583250538451570795891121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree054.table
  base := (-3970180932014968351536716566956578587391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1572708332709940092994371776524000000000000)
      constant := (13888052408469622249624958577416748788244001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351981265448107855483/100000000000000000000)
  centralHi := (87995316362026963871/25000000000000000000)
  directionLo := (355286326365682338693/100000000000000000000)
  directionHi := (177643163182841169347/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree055.table
  base := (-3956810855739206242729552247142408852069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-14116816040994254183790768152280000000000000)
      constant := (124306609041757135344044568487032594575768531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree055.table
  base := (-7916755406076310177906802208289313987189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-28869245139445851728726699690400000000000000)
      constant := (260921374195547059595118765336499494319321411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355286326365682338693/100000000000000000000)
  centralHi := (177643163182841169347/50000000000000000000)
  directionLo := (71712184788470341457/20000000000000000000)
  directionHi := (179280461971175853643/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree056.table
  base := (-246409704519858270108242013172183834159/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-14391285315805379726103452341620000000000000)
      constant := (129654020419914752191853555726226397557639056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree056.table
  base := (-7887940946856666710771811146190216967071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-29429740290112781783554707403368000000000000)
      constant := (272084559009207131568217850595088845668648329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71712184788470341457/20000000000000000000)
  centralHi := (179280461971175853643/50000000000000000000)
  directionLo := (180902942661502680617/50000000000000000000)
  directionHi := (72361177064601072247/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree057.table
  base := (-490712273926301781429299058737928287393/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1629528287846278363157348503440000000000000)
      constant := (15012272394697378907571891985687909799547384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree057.table
  base := (-7853952032924642034004755359579645322719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-3332248382308856870931412790704000000000000)
      constant := (31497156726538601096971089533639082501734209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180902942661502680617/50000000000000000000)
  centralHi := (72361177064601072247/20000000000000000000)
  directionLo := (73004400177067268809/20000000000000000000)
  directionHi := (182511000442668172023/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree058.table
  base := (-7812511528628399078990606836083224532077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-29880447730855261621457641440600000000000000)
      constant := (281351720858637497611012063417107532992067723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree058.table
  base := (-1953704597103545552989506751160127426709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-15275365295723320946605361414652000000000000)
      constant := (147545425735997750397652029480628217126259782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73004400177067268809/20000000000000000000)
  centralHi := (182511000442668172023/50000000000000000000)
  directionLo := (368210026488015759471/100000000000000000000)
  directionHi := (23013126655500984967/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree059.table
  base := (-3884242339962532331697919377093566148637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-15214693140238756353041504909640000000000000)
      constant := (146350209729465879880748166686989634447395163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree059.table
  base := (-7770566351152213270853133862666559921131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-31111225742113571948038730542272000000000000)
      constant := (306933813303963569741708468331457877645138269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368210026488015759471/100000000000000000000)
  centralHi := (23013126655500984967/6250000000000000000)
  directionLo := (371370685545151837141/100000000000000000000)
  directionHi := (185685342772575918571/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree060.table
  base := (-1543868266529205844079771026244583054639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1088)
      previous := (646)
      next := (0)
      square := (16371851479961874453739056908000000000000)
      linear := (-688407218446661417571297293288000000000000)
      constant := (6761487390900180917257003948935315497209329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree060.table
  base := (-7721219259002123147778526182469126673299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-3519080099197833555874082028360000000000000)
      constant := (35444803925885438298620663868466422391416589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371370685545151837141/100000000000000000000)
  centralHi := (185685342772575918571/50000000000000000000)
  directionLo := (1462908870871730631/390625000000000000)
  directionHi := (374504670943163041537/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree061.table
  base := (-7665104138570058575501615849545169263181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-31527263379722014875333746576640000000000000)
      constant := (316051201336090072244087998747433014746466219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree061.table
  base := (-958349724014744970420716392533666189997/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-16116108021723716028847372984104000000000000)
      constant := (165649531884965473495686988115062536959271212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1462908870871730631/390625000000000000)
  centralHi := (374504670943163041537/100000000000000000000)
  directionLo := (188806323407227021171/50000000000000000000)
  directionHi := (377612646814454042343/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree062.table
  base := (-7605793223106828862396536574106242764013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-32076201929344265959959114955320000000000000)
      constant := (328053173349486985040330823365469662570802187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree062.table
  base := (-1901830069035239383128103106010830115987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-16396355597057181056261376840588000000000000)
      constant := (171910625474928362969961824660406861736635626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188806323407227021171/50000000000000000000)
  centralHi := (377612646814454042343/100000000000000000000)
  directionLo := (23793453136297249001/6250000000000000000)
  directionHi := (380695250180755984017/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree063.table
  base := (-754142646756598860628833593013808306847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (544)
      previous := (323)
      next := (0)
      square := (8185925739980937226869528454000000000000)
      linear := (-362501560877405744939827592600000000000000)
      constant := (3780808912460138709458179760133009399321217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree063.table
  base := (-301712118031829898518006737784714511023/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-3705911816086810240816751266016000000000000)
      constant := (39618861625913612920236122957967037657858825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23793453136297249001/6250000000000000000)
  centralHi := (380695250180755984017/100000000000000000000)
  directionLo := (383753092477649187673/100000000000000000000)
  directionHi := (191876546238824593837/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree064.table
  base := (-7472019759877912847917612644295914005089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-33174079028588768129209851712680000000000000)
      constant := (352710046327359663195837766598906327672763511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree064.table
  base := (-7473260207834911409050892792060597473783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-33913701495448222222178769107112000000000000)
      constant := (369544537387079852614757052905027985970690417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383753092477649187673/100000000000000000000)
  centralHi := (191876546238824593837/50000000000000000000)
  directionLo := (386786760970602443937/100000000000000000000)
  directionHi := (193393380485301221969/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree065.table
  base := (-7397587217292370968901265304803578293701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-33723017578211019213835220091360000000000000)
      constant := (365364869248361872912550034698305892858083699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree065.table
  base := (-59189638414639307926623211746591630747/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-34474196646115152277006776820080000000000000)
      constant := (382745566036788356761664853249709396053381625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386786760970602443937/100000000000000000000)
  centralHi := (193393380485301221969/50000000000000000000)
  directionLo := (389796820071817325861/100000000000000000000)
  directionHi := (194898410035908662931/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree066.table
  base := (-3659070692093594866294683176343264851697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1903997562657403905470032692780000000000000)
      constant := (21013179903138465866105524682836796457859567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree066.table
  base := (-3659574018453623347019830469383820528071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1946371766487893462879710251836000000000000)
      constant := (22009600621128612248160596465519275867387481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389796820071817325861/100000000000000000000)
  centralHi := (194898410035908662931/50000000000000000000)
  directionLo := (196391906283120226093/50000000000000000000)
  directionHi := (392783812566240452187/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree067.table
  base := (-7233693407768915312763315512266065433597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-34820894677455521383085956848720000000000000)
      constant := (391327124357866974629880574694215963807214203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree067.table
  base := (-90432499152187454221322582825391505353/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-17797593473724506193331396123008000000000000)
      constant := (204913123378979856907832315279827467783073880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196391906283120226093/50000000000000000000)
  centralHi := (392783812566240452187/100000000000000000000)
  directionLo := (395748260754285932751/100000000000000000000)
  directionHi := (24734266297142870797/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree068.table
  base := (-446515824633533306622137889576192618823/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1440)
      previous := (855)
      next := (0)
      square := (21668626958773069129948751790000000000000)
      linear := (-1040289212561110954932686036100000000000000)
      constant := (11901014758433005280479883877798740234560648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree068.table
  base := (-1429013873654348582382351954757800419267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2844)
      previous := (1746)
      next := (0)
      square := (43337253917546138259897503580000000000000)
      linear := (-2126804829300937790675929409352000000000000)
      constant := (24923873510069499350192609125637482679260745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395748260754285932751/100000000000000000000)
  centralHi := (24734266297142870797/6250000000000000000)
  directionLo := (4983633343976013499/1250000000000000000)
  directionHi := (398690667518081079921/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree069.table
  base := (-3524914773451556625199369498193395061931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-1995487320927779086240927422560000000000000)
      constant := (23231074869158911295502900988512108827101941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree069.table
  base := (-7050564217192198036065682918102128172579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-4079575249864763610702089741328000000000000)
      constant := (48645733271658011217515475483510884958124669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4983633343976013499/1250000000000000000)
  centralHi := (398690667518081079921/100000000000000000000)
  directionLo := (80322303463479893497/20000000000000000000)
  directionHi := (200805758658699733743/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree070.table
  base := (-6950430290324935830463434204970851770663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-36467710326322274636962061984760000000000000)
      constant := (431901641581391063039251752969670814544505537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree070.table
  base := (-34755457286490543306432525966548943591/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-18638336199724901275573407692460000000000000)
      constant := (226071738964231323004449534264260619771980900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80322303463479893497/20000000000000000000)
  centralHi := (200805758658699733743/50000000000000000000)
  directionLo := (20225563856043336081/5000000000000000000)
  directionHi := (404511277120866721621/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree071.table
  base := (-106969724666714651357088565103249383539/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-18508324437972262860793715181720000000000000)
      constant := (222930682754131887327019986799176347309281952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree071.table
  base := (-1711664318801290466006888729775041880409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-18918583775058366302987411548944000000000000)
      constant := (233350734515207861010599307853549032138112382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20225563856043336081/5000000000000000000)
  centralHi := (404511277120866721621/100000000000000000000)
  directionLo := (40739039727750752827/10000000000000000000)
  directionHi := (407390397277507528271/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree072.table
  base := (-1347346398672437941616440558391414726803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1088)
      previous := (646)
      next := (0)
      square := (16371851479961874453739056908000000000000)
      linear := (-834790831679261706804728860936000000000000)
      constant := (10223077852168732648497670798880881143953933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree072.table
  base := (-3368633578021837018132324437097958649913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2133203483376870147822379489492000000000000)
      constant := (26749197693553187558833823413659489950175143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40739039727750752827/10000000000000000000)
  centralHi := (407390397277507528271/100000000000000000000)
  directionLo := (410249312333239863739/100000000000000000000)
  directionHi := (20512465616661993187/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree073.table
  base := (-6622444629272786985399486943479924740097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-38114525975189027890838167120800000000000000)
      constant := (474433040807220488891974972532268715751007703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree073.table
  base := (-206966436356872431756819012016429118407/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-19479078925725296357815419261912000000000000)
      constant := (248247866819423846495159184938049485808374288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410249312333239863739/100000000000000000000)
  centralHi := (20512465616661993187/5000000000000000000)
  directionLo := (413088441796507995979/100000000000000000000)
  directionHi := (20654422089825399799/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree074.table
  base := (-3251602585681819292057534177848014169709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-19331732262405639487731767749740000000000000)
      constant := (244522482590679944051954599844377315144586891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree074.table
  base := (-203238687820422351910198128172534290743/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-19759326501058761385229423118396000000000000)
      constant := (255865991638591367922125472798704612956439312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413088441796507995979/100000000000000000000)
  centralHi := (20654422089825399799/5000000000000000000)
  directionLo := (51988523857109223729/12500000000000000000)
  directionHi := (415908190856873789833/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree075.table
  base := (-6379017962769007515407155359548809656939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-4356933674937058895565433764240000000000000)
      constant := (55986029463724327636235927505590394009144629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree075.table
  base := (-3189703560766090398937352694855227095193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2226619341821358490293714108320000000000000)
      constant := (29288572080564969966470941300036839369489223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51988523857109223729/12500000000000000000)
  centralHi := (415908190856873789833/100000000000000000000)
  directionLo := (418708951060051420031/100000000000000000000)
  directionHi := (3271163680156651719/781250000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree076.table
  base := (-390617929079248525911395949800977669269/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-19880670812027890572357136128420000000000000)
      constant := (259460465369605138412092491350541256657850648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree076.table
  base := (-625023668990626063792651453746953135013/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-20319821651725691440057430831364000000000000)
      constant := (271441333666762156575490276662897674479155935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418708951060051420031/100000000000000000000)
  centralHi := (3271163680156651719/781250000000000000)
  directionLo := (21074555047128475237/5000000000000000000)
  directionHi := (421491100942569504741/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree077.table
  base := (-1528953828249901064352392756244906695309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-20155140086839016114669820317760000000000000)
      constant := (267092476473119090001059515984223995371002582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree077.table
  base := (-1529032431235059959840029442855096842111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-20600069227059156467471434687848000000000000)
      constant := (279398542549685035735849993216680986227338578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21074555047128475237/5000000000000000000)
  centralHi := (421491100942569504741/100000000000000000000)
  directionLo := (424255006628973202641/100000000000000000000)
  directionHi := (212127503314486601321/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree078.table
  base := (-5976806360175889532717793789310856113947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-4539913191477809257107223223800000000000000)
      constant := (61074035983399694465609049551529162583069317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree078.table
  base := (-5977088896745126582155425422698875880463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-4640070400531693665530097454296000000000000)
      constant := (63881949311416444675834166216897624870546193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424255006628973202641/100000000000000000000)
  centralHi := (212127503314486601321/50000000000000000000)
  directionLo := (213500511197116853991/50000000000000000000)
  directionHi := (427001022394233707983/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree079.table
  base := (-5832862723463428970135658499983936713307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-41408157272922534398590377392880000000000000)
      constant := (565365036386237669295508093005561780608688493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree079.table
  base := (-1458279143658251150435159715986848516221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-21160564377726086522299442400816000000000000)
      constant := (295652018640538687593777165055851214018618358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213500511197116853991/50000000000000000000)
  centralHi := (427001022394233707983/100000000000000000000)
  directionLo := (107432372798452741639/25000000000000000000)
  directionHi := (429729491193810966557/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree080.table
  base := (-5683986819629670907663251101564072179243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-41957095822544785483215745771560000000000000)
      constant := (581281084267147304190060749552031848261788957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree080.table
  base := (-2842107430680927314293867391633518193157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-21440811953059551549713446257300000000000000)
      constant := (303948280032542341453441438773241219179598643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107432372798452741639/25000000000000000000)
  centralHi := (429729491193810966557/100000000000000000000)
  directionLo := (432440745163614800563/100000000000000000000)
  directionHi := (108110186290903700141/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree081.table
  base := (-5530180798983054068355134085877679157747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-4722892708018559618649012683360000000000000)
      constant := (66379384655597100639497166506881350723411117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree081.table
  base := (-5530385623473908208953018541592980404363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-4826902117420670350472766691952000000000000)
      constant := (69412789699988175665408943112514028663139093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432440745163614800563/100000000000000000000)
  centralHi := (108110186290903700141/25000000000000000000)
  directionLo := (435135106091927749429/100000000000000000000)
  directionHi := (43513510609192774943/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree082.table
  base := (-134286164376928978673435400765774844983/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-4305497292178928765246648252892000000000000)
      constant := (61376516430876461060476673162464878512796868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree082.table
  base := (-268581525908667964793850584386130293751/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-22001307103726481604541453970268000000000000)
      constant := (320879837337557980480544382480855951059536490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435135106091927749429/100000000000000000000)
  centralHi := (43513510609192774943/10000000000000000000)
  directionLo := (437812885865187844703/100000000000000000000)
  directionHi := (13681652683287120147/3125000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree083.table
  base := (-208311434043858004719159436556884959853/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-8720782294282307747418370181520000000000000)
      constant := (126066637412467325588016753701629711097111735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree083.table
  base := (-2603975508569188058746368299526993756187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-22281554679059946631955457826752000000000000)
      constant := (329515129181458453631366858595063489240157613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437812885865187844703/100000000000000000000)
  centralHi := (13681652683287120147/3125000000000000000)
  directionLo := (440474386889379504283/100000000000000000000)
  directionHi := (110118596722344876071/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree084.table
  base := (-503920014329450548558897484596574440721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (544)
      previous := (323)
      next := (0)
      square := (8185925739980937226869528454000000000000)
      linear := (-490587222455930998019080214292000000000000)
      constant := (7190205846859048889691530657719589986631631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree084.table
  base := (-2519674213808640007772954727706293855123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2506866917154823517707717964804000000000000)
      constant := (37584825275730196449096374273008081075869453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440474386889379504283/100000000000000000000)
  centralHi := (110118596722344876071/25000000000000000000)
  directionLo := (443119902488644217069/100000000000000000000)
  directionHi := (44311990248864421707/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree085.table
  base := (-973138160362836062778928084211912014763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (576)
      previous := (342)
      next := (0)
      square := (8667450783509227651979500716000000000000)
      linear := (-525903394948894598898148090176000000000000)
      constant := (7813190332493839540934514196255577461741261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree085.table
  base := (-1216455977779706629722362135275697921517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1422)
      previous := (873)
      next := (0)
      square := (21668626958773069129948751790000000000000)
      linear := (-1343649989983933922751968561160000000000000)
      constant := (20419101807491516890986628931655636436015798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443119902488644217069/100000000000000000000)
  centralHi := (44311990248864421707/10000000000000000000)
  directionLo := (445749717282598329489/100000000000000000000)
  directionHi := (44574971728259832949/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree086.table
  base := (-1171814757295578671679530350243682525423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-22625363560139145995483978021820000000000000)
      constant := (340670570034275099801825114024832363502749554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree086.table
  base := (-117184462499278745210539278663243139567/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-23122297405060341714197469396204000000000000)
      constant := (356099037576267772443824697152110891879724660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445749717282598329489/100000000000000000000)
  centralHi := (44574971728259832949/10000000000000000000)
  directionLo := (112091026885932957007/25000000000000000000)
  directionHi := (448364107543731828029/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree087.table
  base := (-4503905896738895290154747293421386433967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-5088851741100060341732591602480000000000000)
      constant := (77642045427831178952705930138781219320583537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree087.table
  base := (-900802622398518972731784168571336424793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-5200565551198623720358105167264000000000000)
      constant := (81152521518818881397147108763260018866174115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112091026885932957007/25000000000000000000)
  centralHi := (448364107543731828029/100000000000000000000)
  directionLo := (11274083538403961463/2500000000000000000)
  directionHi := (450963341536158458521/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree088.table
  base := (-2157816179615762012240559692104429762963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-23174302109761397080109346400500000000000000)
      constant := (358216491062234540674461848167716378186533237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree088.table
  base := (-2157864281744950612106164635970030623329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-23682792555727271769025477109172000000000000)
      constant := (374386657441000453905520682135589150348721271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11274083538403961463/2500000000000000000)
  centralHi := (450963341536158458521/100000000000000000000)
  directionLo := (226773839918446436133/50000000000000000000)
  directionHi := (453547679836892872267/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree089.table
  base := (-4122439267780242280036112233146187001363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-46897542769145045244844061179680000000000000)
      constant := (734304857676752384271089790578806767609454837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree089.table
  base := (-1030631395193652573336472596897144260579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-23963040131060736796439480965656000000000000)
      constant := (383699968450646075703955821067939855556468042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226773839918446436133/50000000000000000000)
  centralHi := (453547679836892872267/100000000000000000000)
  directionLo := (114029343910185970863/25000000000000000000)
  directionHi := (456117375640743883453/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree090.table
  base := (-981081845348709693602804806847378587317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2635915628820405351637190531020000000000000)
      constant := (41799668529619225493688676648842215176530774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree090.table
  base := (-1962202405183391436224621397952532353767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2693698634043800202650387202460000000000000)
      constant := (43680697669202499178917797913831718149761337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114029343910185970863/25000000000000000000)
  centralHi := (456117375640743883453/100000000000000000000)
  directionLo := (91734535009966719123/20000000000000000000)
  directionHi := (14333521095307299863/3125000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree091.table
  base := (-3721297377206410231749077616913198722189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-47995419868389547414094797937040000000000000)
      constant := (770700507932432122615347864149308770123586411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree091.table
  base := (-3721366828035814822735192445635861835503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-49047070563455333702534977357248000000000000)
      constant := (805331176817483210613853016937762723365856697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91734535009966719123/20000000000000000000)
  centralHi := (14333521095307299863/3125000000000000000)
  directionLo := (461213817348679421243/100000000000000000000)
  directionHi := (115303454337169855311/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree092.table
  base := (-1715502861111748686238235940970873063/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-24272179209005899249360083157860000000000000)
      constant := (394612139651358640722067653137715593383052288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree092.table
  base := (-702682429362208527034199967602399522503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-49607565714122263757362985070216000000000000)
      constant := (824635791882417523374903761038553194209848485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461213817348679421243/100000000000000000000)
  centralHi := (115303454337169855311/25000000000000000000)
  directionLo := (11593525881642731597/2500000000000000000)
  directionHi := (463741035265709263881/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree093.table
  base := (-165024268403698433501509960852350126031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (544)
      previous := (323)
      next := (0)
      square := (8185925739980937226869528454000000000000)
      linear := (-545481077418156106481617052160000000000000)
      constant := (8977392736004774314147642337741341627154082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree093.table
  base := (-103141913252490183290952712156712750289/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2787114492488288545121721821288000000000000)
      constant := (46898133447265764746648728011554160242663664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11593525881642731597/2500000000000000000)
  centralHi := (463741035265709263881/100000000000000000000)
  directionLo := (466254555222018805341/100000000000000000000)
  directionHi := (233127277611009402671/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree094.table
  base := (-616540876969073603048644775597081369577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-9928447103451260133594180614616000000000000)
      constant := (165384741498331880528562084528335991357730223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree094.table
  base := (-616550893575251431507710128148198965907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-50728556015456123867019000496152000000000000)
      constant := (863923006261284169420127928459234272448379465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466254555222018805341/100000000000000000000)
  centralHi := (233127277611009402671/50000000000000000000)
  directionLo := (46875459756812344687/10000000000000000000)
  directionHi := (468754597568123446871/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree095.table
  base := (-1430003670396075776108862860352447246407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-25095587033439275876298135725880000000000000)
      constant := (423049680967790331860936422242873284712095393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree095.table
  base := (-57201044849113713171162750420505730667/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-25644525583061526960923504104560000000000000)
      constant := (441952801783245832302840935456916614863378325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46875459756812344687/10000000000000000000)
  centralHi := (468754597568123446871/100000000000000000000)
  directionLo := (471241376809405547513/100000000000000000000)
  directionHi := (235620688404702773757/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree096.table
  base := (-2632394621331508495636683524744676324729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-5637790290722311426357959981160000000000000)
      constant := (96165812063302595818120516458148788542153319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree096.table
  base := (-1316217436615935616052433865891247776853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2880530350932776887593056440116000000000000)
      constant := (50228566284444705413931254620360629392489483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471241376809405547513/100000000000000000000)
  centralHi := (235620688404702773757/50000000000000000000)
  directionLo := (118428775455227446231/25000000000000000000)
  directionHi := (18948604072836391397/4000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree097.table
  base := (-47997331428156889650817760033970085439/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-5128905116612305392184700820912000000000000)
      constant := (88510254649688709950450273691360219038865805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree097.table
  base := (-2399902651154060210351137905814006274229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-52410041467456914031503023635056000000000000)
      constant := (924548774165064278245389661575292169680730371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118428775455227446231/25000000000000000000)
  centralHi := (18948604072836391397/4000000000000000000)
  directionLo := (238087988026047686147/50000000000000000000)
  directionHi := (95235195210419074459/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree098.table
  base := (-2162423499962936556868081598639392446323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-51837989715745305006472376587800000000000000)
      constant := (904930074913514313054845042751698940247113877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree098.table
  base := (-2162455836585171295847833102215613727363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-52970536618123844086331031348024000000000000)
      constant := (945209346024466455444228254101527588695128837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238087988026047686147/50000000000000000000)
  centralHi := (95235195210419074459/20000000000000000000)
  directionLo := (478624197722113174363/100000000000000000000)
  directionHi := (119656049430528293591/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree099.table
  base := (-192006568390779374722727723705669274837/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (544)
      previous := (323)
      next := (0)
      square := (8185925739980937226869528454000000000000)
      linear := (-582076980726306178789974944072000000000000)
      constant := (10277498812215105205896661366987061579572107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree099.table
  base := (-15000739552647509043915520823568974821/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-2973946209377265230064391058944000000000000)
      constant := (53671994893979025335063395989796468241710784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478624197722113174363/100000000000000000000)
  centralHi := (119656049430528293591/25000000000000000000)
  directionLo := (30066247500383636327/6250000000000000000)
  directionHi := (481059960006138181233/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree100.table
  base := (-1672793371651888259797866933182742474757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-52935866814989807175723113345160000000000000)
      constant := (945237000408309528723793579110791686823157043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree100.table
  base := (-167281933872579560936635865183263011263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-27045763459728852097993523386980000000000000)
      constant := (493604229911317797142353585706491664538524685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30066247500383636327/6250000000000000000)
  centralHi := (481059960006138181233/100000000000000000000)
  directionLo := (483483451213253054921/100000000000000000000)
  directionHi := (241741725606626527461/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree101.table
  base := (-35515169655980009624593833333481804383/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-5348480536461205826034848172384000000000000)
      constant := (96571639626022710089878666021448455307199268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree101.table
  base := (-56825202090131546560000516538044434473/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-54652022070124634250815054486928000000000000)
      constant := (1008547000729278990397330142212447260648393175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483483451213253054921/100000000000000000000)
  centralHi := (241741725606626527461/50000000000000000000)
  directionLo := (242947427478173159691/50000000000000000000)
  directionHi := (485894854956346319383/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree102.table
  base := (-581753064067496917137453734690138473253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (160)
      previous := (95)
      next := (0)
      square := (2407625217641452125549861310000000000000)
      linear := (-176580862464818004395339379420000000000000)
      constant := (3223572157299679850137559972830267645954699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree102.table
  base := (-36360217875578242408616568766080455593/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (158)
      previous := (97)
      next := (0)
      square := (2407625217641452125549861310000000000000)
      linear := (-180433062813044327796219157516000000000000)
      constant := (3366377550237814948670376394390026116078704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242947427478173159691/50000000000000000000)
  centralHi := (485894854956346319383/100000000000000000000)
  directionLo := (122073587578614750443/25000000000000000000)
  directionHi := (488294350314459001773/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree103.table
  base := (-36059663108093185204468344703176687737/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-10916536492771312085919843696240000000000000)
      constant := (201465410311922001346869245405587187175980315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree103.table
  base := (-901510249829504192207342692208548840023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-55773012371458494360471069912864000000000000)
      constant := (1051902048358259973319422697327623964467100177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122073587578614750443/25000000000000000000)
  centralHi := (488294350314459001773/100000000000000000000)
  directionLo := (490682111987985953227/100000000000000000000)
  directionHi := (122670527996996488307/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree104.table
  base := (-2538253189611867220024865851636888987/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-5513162101347881151422458685988000000000000)
      constant := (102845831011538798343198141899949311293620325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree104.table
  base := (-634580022485567095582320001549373970653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-56333507522125424415299077625832000000000000)
      constant := (1073918554329929867670979095681819678302331547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490682111987985953227/100000000000000000000)
  centralHi := (122670527996996488307/25000000000000000000)
  directionLo := (24652915522355625067/5000000000000000000)
  directionHi := (493058310447112501341/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree105.table
  base := (-45340179219178210636344914992730746071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3093364420172281255491664179920000000000000)
      constant := (58322603078885916381484930091918403257541924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree105.table
  base := (-72547282688815630110414943323800484749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-6321555852532483830014120593200000000000000)
      constant := (121795671996296488576156371956037108299537695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24652915522355625067/5000000000000000000)
  centralHi := (493058310447112501341/100000000000000000000)
  directionLo := (30963944504615209421/6250000000000000000)
  directionHi := (495423112073843350737/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree106.table
  base := (-85966119063549952854729741507301363819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-56229498112723313683475323617240000000000000)
      constant := (1071372687129147637620433284963139509152706781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree106.table
  base := (-42989767149175548077669785947046714273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-28727248911729642262477546525884000000000000)
      constant := (559314764489110676413733854626396531496175927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30963944504615209421/6250000000000000000)
  centralHi := (495423112073843350737/100000000000000000000)
  directionLo := (15555521228061206371/3125000000000000000)
  directionHi := (497776679297958603873/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree107.table
  base := (39140505403630278035405690183535676469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-11355687332469112953620138399184000000000000)
      constant := (218631160986357127956025786029131376294495869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree107.table
  base := (39138102782415933652559273985705795299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-58014992974126214579783100764736000000000000)
      constant := (1141323997101784905624463603975122503867863495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15555521228061206371/3125000000000000000)
  centralHi := (497776679297958603873/100000000000000000000)
  directionLo := (500119170727211286121/100000000000000000000)
  directionHi := (250059585363605643061/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree108.table
  base := (241142198065407296112223036599325215259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2720)
      previous := (1615)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3184854178442656436262558909700000000000000)
      constant := (61953122697000771929301984291897204987209851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree108.table
  base := (241136819769801925062112071286520720533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3254193784710730257478394915428000000000000)
      constant := (64680247338832423400299965019446604488234037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500119170727211286121/100000000000000000000)
  centralHi := (250059585363605643061/50000000000000000000)
  directionLo := (251225370636030852019/50000000000000000000)
  directionHi := (502450741272061704039/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree109.table
  base := (193444847495006723173152622398880315091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-28938156880795033468675714376640000000000000)
      constant := (568686948858084317436023139261528975399103382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree109.table
  base := (386884879649103021266159165015710174139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-29567991637730037344719558095336000000000000)
      constant := (593695446876595286748468442835252662162935539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251225370636030852019/50000000000000000000)
  centralHi := (502450741272061704039/100000000000000000000)
  directionLo := (63096442783153278857/12500000000000000000)
  directionHi := (504771542265226230857/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree110.table
  base := (133773427406513857054316496049071846663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-29212626155606159010988398565980000000000000)
      constant := (579904436104972492602571646830094543492681852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree110.table
  base := (1070178797349680696308760703269368081843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-59696478426127004744267123903640000000000000)
      constant := (1210763321867150589865663344222803626380873643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63096442783153278857/12500000000000000000)
  centralHi := (504771542265226230857/100000000000000000000)
  directionLo := (507081721576301596033/100000000000000000000)
  directionHi := (253540860788150798017/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree111.table
  base := (1371508402648772189748916271339534357117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-6552687873426063234066907278960000000000000)
      constant := (131384570201765120252089966261317125429206813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree111.table
  base := (1371500684493118766052501174458934121233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-6695219286310437199899459068512000000000000)
      constant := (137151304028985789542721179414277031961036337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507081721576301596033/100000000000000000000)
  centralHi := (253540860788150798017/50000000000000000000)
  directionLo := (509381423721710362161/100000000000000000000)
  directionHi := (254690711860855181081/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree112.table
  base := (419435566507171209756204733681387395719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-29761564705228410095613766944660000000000000)
      constant := (602665338170575168498801710023970577232530238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree112.table
  base := (41943383936147692739967640260306505429/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-30408734363730432426961569664788000000000000)
      constant := (629093068384878523165623981803576344412416580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509381423721710362161/100000000000000000000)
  centralHi := (254690711860855181081/50000000000000000000)
  directionLo := (255835394985099458449/50000000000000000000)
  directionHi := (511670789970198916899/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree113.table
  base := (397777788328817458176333462691575024913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-12014413592015814255170580453600000000000000)
      constant := (245683501121905164339044319059712786639798713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree113.table
  base := (994441379102913944177336198214474536547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-30688981939063897454375573521272000000000000)
      constant := (641118261621470818962977886979473048269558747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255835394985099458449/50000000000000000000)
  centralHi := (511670789970198916899/100000000000000000000)
  directionLo := (128487489611026477797/25000000000000000000)
  directionHi := (513949958444105911189/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree114.table
  base := (2304948367461796422751059160172661094559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-6735667389966813595608696738520000000000000)
      constant := (139080179939962691895540423095369899056327551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree114.table
  base := (576235708371254170593129238847663632987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3441025501599706942421064153084000000000000)
      constant := (72584049752323563888562755444377149579866486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128487489611026477797/25000000000000000000)
  centralHi := (513949958444105911189/100000000000000000000)
  directionLo := (258109532108303282957/50000000000000000000)
  directionHi := (103243812843321313183/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree115.table
  base := (2625920486559228741821879820137976845379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-61169945059323573445103639025360000000000000)
      constant := (1275243017743509913426728348510278877774830779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree115.table
  base := (2625915534207624275400243475507064909759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-62498954179461655018407162468480000000000000)
      constant := (1331015253538758297163697994620213875830283159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258109532108303282957/50000000000000000000)
  centralHi := (103243812843321313183/20000000000000000000)
  directionLo := (518478239405126581191/100000000000000000000)
  directionHi := (64809779925640822649/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree116.table
  base := (2951805246587070049063519760399210126193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-61718883608945824529729007404040000000000000)
      constant := (1298981700324902314564136601859198345538227993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree116.table
  base := (1475900407531958781654265804606923698211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-31529724665064292536617585090724000000000000)
      constant := (677871798557946731815410300799603408539046811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518478239405126581191/100000000000000000000)
  centralHi := (64809779925640822649/12500000000000000000)
  directionLo := (130181903315277113829/25000000000000000000)
  directionHi := (520727613261108455317/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree117.table
  base := (3282602599291168263150711606637981933989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-6918646906507563957150486198080000000000000)
      constant := (146993074119814708989840171940498376778922821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree117.table
  base := (328259863411441470880736537853016199857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3534441360044195284892398771912000000000000)
      constant := (76705440342452503174261449298724408408793365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130181903315277113829/25000000000000000000)
  centralHi := (520727613261108455317/100000000000000000000)
  directionLo := (10459346245126055963/2000000000000000000)
  directionHi := (522967312256302798151/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree118.table
  base := (1809156250043526736294179011990915489473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-31408380354095163349489872080700000000000000)
      constant := (673555458943917953110102218579068371188119273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree118.table
  base := (11307215476369889547693649177032938533/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-32090219815731222591445592803692000000000000)
      constant := (702939120291140102091523698427485227699893280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10459346245126055963/2000000000000000000)
  centralHi := (522967312256302798151/100000000000000000000)
  directionLo := (262598730082873827741/50000000000000000000)
  directionHi := (525197460165747655483/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree119.table
  base := (79178698153624518414538650642730481167/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 153000000000000000000000000000000000000000
      center := (288)
      previous := (171)
      next := (0)
      square := (4333725391754613825989750358000000000000)
      linear := (-372739407398897516374147720824000000000000)
      constant := (8067655603800049986070705015087688818092755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree119.table
  base := (3958931733821534184946354391596865892103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2844)
      previous := (1746)
      next := (0)
      square := (43337253917546138259897503580000000000000)
      linear := (-3808290281301727955159952548256000000000000)
      constant := (84193208251535628480619955581739120481491759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262598730082873827741/50000000000000000000)
  centralHi := (525197460165747655483/100000000000000000000)
  directionLo := (263709089073794949761/50000000000000000000)
  directionHi := (527418178147589899523/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree120.table
  base := (4304469783734006930763209436166146837149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-7101626423048314318692275657640000000000000)
      constant := (155123252361458738989515844850252016435936061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree120.table
  base := (4304466944478839395896444864535212398369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-7255714436977367254727466781480000000000000)
      constant := (161879647239749610430019228683930676383128641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263709089073794949761/50000000000000000000)
  centralHi := (527418178147589899523/100000000000000000000)
  directionLo := (529629584819894342999/100000000000000000000)
  directionHi := (529629584819894343/100000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree121.table
  base := (290932318284958059426295342882578382921/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-32231788178528539976427924648720000000000000)
      constant := (710467186808188452169321004753550690991820168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree121.table
  base := (4654914552807867222066501719411285448259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-65861925083463235347375208746288000000000000)
      constant := (1482775095145004756897163873581226353450921659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529629584819894342999/100000000000000000000)
  centralHi := (529629584819894343/100000000000000000)
  directionLo := (531831796334578360413/100000000000000000000)
  directionHi := (265915898167289180207/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree122.table
  base := (313142300053584819892114172146739585209/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-32506257453339665518740608838060000000000000)
      constant := (722988379824570193726664372131789357289028872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree122.table
  base := (1252568632292445828761402226157755947807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-33211210117065082701101608229628000000000000)
      constant := (754429675080394932555647449258459846440492014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531831796334578360413/100000000000000000000)
  centralHi := (265915898167289180207/50000000000000000000)
  directionLo := (534024926448602413197/100000000000000000000)
  directionHi := (267012463224301206599/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree123.table
  base := (5370548877476293269123772386692312433383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-7284605939589064680234065117200000000000000)
      constant := (163470714363377030358349120328894078293247687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree123.table
  base := (5370546845694521869462563533951967082961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5372)
      previous := (3298)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-7442546153866343939670136019136000000000000)
      constant := (170574398903623530816977292695037718486975729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534024926448602413197/100000000000000000000)
  centralHi := (267012463224301206599/50000000000000000000)
  directionLo := (536209086592539941911/100000000000000000000)
  directionHi := (67026135824067492739/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree124.table
  base := (5735733293200120602090617639438807464691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48960)
      previous := (29070)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-66110392005923833206731954433480000000000000)
      constant := (1496713382404144701953952889318100338215661291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree124.table
  base := (1147146295221501335824781508806200464483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-67543410535464025511859231885192000000000000)
      constant := (1561705814992130320909356896373730237040601415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536209086592539941911/100000000000000000000)
  centralHi := (67026135824067492739/12500000000000000000)
  directionLo := (538384385936643576953/100000000000000000000)
  directionHi := (269192192968321788477/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree125.table
  base := (305291501027970448837397223352520026637/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (73673331659828435041825756086000000000000)
      linear := (-6665933055554608429135732281216000000000000)
      constant := (152240761897894668584451205000129809178565674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree125.table
  base := (11925446085108332143490626403893367157/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-34051952843065477783343619799080000000000000)
      constant := (794234012337377078062114888935040821881691392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538384385936643576953/100000000000000000000)
  centralHi := (269192192968321788477/50000000000000000000)
  directionLo := (16892216607953703147/3125000000000000000)
  directionHi := (108110186290903700141/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree126.table
  base := (6480839033662622168609661168068503412713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-7467585456129815041775854576760000000000000)
      constant := (172035459880828371019659026721571797486274057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree126.table
  base := (1620209395142295462734201289529403066901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3814688935377660312306402628396000000000000)
      constant := (89747567728849099254445336920343194972668778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16892216607953703147/3125000000000000000)
  centralHi := (108110186290903700141/20000000000000000000)
  directionLo := (542708827984508041851/100000000000000000000)
  directionHi := (135677206996127010463/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree127.table
  base := (3430380154022826920421448115257723308059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (24480)
      previous := (14535)
      next := (0)
      square := (368366658299142175209128780430000000000000)
      linear := (-33878603827395293230304029784760000000000000)
      constant := (787223971093019760684554080996995338324261459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree127.table
  base := (6860759008741258698367913526714510351607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-69224895987464815676343255024096000000000000)
      constant := (1642670398267593636942326092582930841424529807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542708827984508041851/100000000000000000000)
  centralHi := (135677206996127010463/25000000000000000000)
  directionLo := (68107272286111396529/12500000000000000000)
  directionHi := (544858178288891172233/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree128.table
  base := (1449118764107514507247876477377323924437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (9792)
      previous := (5814)
      next := (0)
      square := (147346663319656870083651512172000000000000)
      linear := (-13661229240882567509046685589640000000000000)
      constant := (320158805738886327940168822267610419527460637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree128.table
  base := (7245592658817217558491771006274717738413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (48348)
      previous := (29682)
      next := (0)
      square := (736733316598284350418257560860000000000000)
      linear := (-69785391138131745731171262737064000000000000)
      constant := (1670110562064348787224819830637918940837612213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell016.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68107272286111396529/12500000000000000000)
  centralHi := (544858178288891172233/100000000000000000000)
  directionLo := (273499541555493242493/50000000000000000000)
  directionHi := (546999083110986484987/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree129.table
  base := (7635339549140781209441172469736164250209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (5440)
      previous := (3230)
      next := (0)
      square := (81859257399809372268695284540000000000000)
      linear := (-7650564972670565403317644036320000000000000)
      constant := (180817488710601771584129229771533751468310401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree129.table
  base := (763533851049841054362425405314075464771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (2686)
      previous := (1649)
      next := (0)
      square := (40929628699904686134347642270000000000000)
      linear := (-3908104793822148654777737247224000000000000)
      constant := (94320928358708469681757270744116039046594095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell016.Kernel129
