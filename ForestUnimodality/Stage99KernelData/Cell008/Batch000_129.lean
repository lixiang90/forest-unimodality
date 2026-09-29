import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell008.Parameters
import ForestUnimodality.BinomialMassData.Q13_42.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_42.Batch050_099
import ForestUnimodality.BinomialMassData.Q13_42.Batch100_149
import ForestUnimodality.BinomialMassData.Q20_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q20_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q20_63.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree000.table
  base := (3306912572465811628870113759/500000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (673095305238265440017642040000000000000)
      constant := (132276502898632465154804550360000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree000.table
  base := (3306912572465811628870113759/500000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (1009642957857398160026463060000000000000)
      constant := (198414754347948697732206825540000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree001.table
  base := (46349823004066599318541455169134448223733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (64006913088678055248625930260000000000000)
      constant := (13601629213213876152340403878870527777777502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree001.table
  base := (9169546474985122797170509923112603930461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (283999790039665060414897365060000000000000)
      constant := (60540795593224241644713626700989874999999515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29430762067163647193/100000000000000000000)
  directionHi := (14715381033581823597/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree002.table
  base := (8108957909872374304925533826700809004157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (29068816307331090814658480640000000000000)
      constant := (9496511174859778148390897442420151388888632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree002.table
  base := (3173699125864137977036541142330091175359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (122747035664217532258124520660000000000000)
      constant := (41807722108173234286723663208227106249999570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/100000000000000000000)
  centralHi := (14715381033581823597/50000000000000000000)
  directionLo := (41621382866358456343/100000000000000000000)
  directionHi := (5202672858294807043/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree003.table
  base := (2826347917053660817526399734603948097617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1956426824671957873102989660000000000000)
      constant := (2201452189801640094049950995004495308531728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree003.table
  base := (21879567092854278062942347451412771122403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-4278413190136666210960924860000000000000)
      constant := (3194775366580590378285698520557677354993241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41621382866358456343/100000000000000000000)
  centralHi := (5202672858294807043/12500000000000000000)
  directionLo := (50975575205798275593/100000000000000000000)
  directionHi := (25487787602899137797/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree004.table
  base := (15634178953443847142339307086098519705027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-40807377255362838053276418600000000000000)
      constant := (4560458649265319233124845783472964793277938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree004.table
  base := (7476067431719663081874993270243676294783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-199758473086677524055421168140000000000000)
      constant := (19625805172693126886376947087464767475995818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/100000000000000000000)
  centralHi := (25487787602899137797/50000000000000000000)
  directionLo := (29430762067163647193/50000000000000000000)
  directionHi := (58861524134327294387/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree005.table
  base := (425830691925530518211959193001739800181/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-75745474036709802487243868220000000000000)
      constant := (3111903563876869676504355803587787531330350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree005.table
  base := (2511807625895699087187805932674379166407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-361011227462125052212194012540000000000000)
      constant := (13225627768182112953239554553712814548625844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/50000000000000000000)
  centralHi := (58861524134327294387/100000000000000000000)
  directionLo := (13161836922360029269/20000000000000000000)
  directionHi := (32904592305900073173/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree006.table
  base := (7081734863749017865815802181064333928381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-36894523606018922307070439280000000000000)
      constant := (697643380750365958328568451684304724981338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree006.table
  base := (3287649866785254852990084370691278656821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-58029331315285842263218539660000000000000)
      constant := (974718419292268100514248471383235925105374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13161836922360029269/20000000000000000000)
  centralHi := (32904592305900073173/50000000000000000000)
  directionLo := (72090349805809597099/100000000000000000000)
  directionHi := (720903498058095971/1000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree007.table
  base := (4492779827880674555304788708192641986089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-2971870767334770027656709540000000000000)
      constant := (27988645889872352181732830954155851916534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree007.table
  base := (1018495346401998903491590384173319878133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-13949321147204492010729381660000000000000)
      constant := (115400313551958002210970888290718546838364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/100000000000000000000)
  centralHi := (720903498058095971/1000000000000000000)
  directionLo := (77866477324828239913/100000000000000000000)
  directionHi := (38933238662414119957/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree008.table
  base := (80909467027823582064418766044497326479/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-180559764380750695789146217080000000000000)
      constant := (862243104715805573336831454146630847514432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree008.table
  base := (561924574651744191907610249715524673131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-844769490588467636682512545740000000000000)
      constant := (3481027955308909689747571646294556570209252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77866477324828239913/100000000000000000000)
  centralHi := (38933238662414119957/50000000000000000000)
  directionLo := (83242765732716912687/100000000000000000000)
  directionHi := (5202672858294807043/6250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree009.table
  base := (1168597735452895229866356597742390430189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-71832620387365886741037888900000000000000)
      constant := (168636401888560315635001651173754262158522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree009.table
  base := (446289885230157645694821358357473216539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-111780249440435018315476154460000000000000)
      constant := (220220289836841359940248142957097125662466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83242765732716912687/100000000000000000000)
  centralHi := (5202672858294807043/6250000000000000000)
  directionLo := (88292286201490941579/100000000000000000000)
  directionHi := (4414614310074547079/5000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree010.table
  base := (45096304564788132673657471382978327811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-250435957943444624657081116320000000000000)
      constant := (260966903864387667805960661473191256752868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree010.table
  base := (-16516947271020629189571352764314019499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-1167274999339362692996058234540000000000000)
      constant := (971252018852168620061367318342500417622584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88292286201490941579/100000000000000000000)
  centralHi := (4414614310074547079/5000000000000000000)
  directionLo := (93068241406722553139/100000000000000000000)
  directionHi := (4653412070336127657/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree011.table
  base := (-18617850525221992815700562453831865693/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-285374054724791589091048565940000000000000)
      constant := (98427332754718167170802952287937259450320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree011.table
  base := (-923785631155492243441403427197532523249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-1328527753714810221152831078940000000000000)
      constant := (320058165901390739449685101417664471741573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93068241406722553139/100000000000000000000)
  centralHi := (4653412070336127657/5000000000000000000)
  directionLo := (19522159014201257133/20000000000000000000)
  directionHi := (48805397535503142833/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree012.table
  base := (-56206524491560258727781146328378251503/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-106770717168712851175005338520000000000000)
      constant := (-669183039109493885373605464526716182350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree012.table
  base := (-1549818170471266695886877919797071648471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-165531167565584194367733769260000000000000)
      constant := (-6759151762949186149776617410169532325237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19522159014201257133/20000000000000000000)
  centralHi := (48805397535503142833/50000000000000000000)
  directionLo := (50975575205798275593/50000000000000000000)
  directionHi := (101951150411596551187/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree013.table
  base := (-969803855367242307484442724224944310591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-355250248287485517958983465180000000000000)
      constant := (-54582937282714379078115126419267254627508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree013.table
  base := (-41141827295164650716070210573201112209/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-1651033262465705277466376767740000000000000)
      constant := (-233412933565982128101189626617253572625350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/50000000000000000000)
  centralHi := (101951150411596551187/100000000000000000000)
  directionLo := (53057060854569541129/50000000000000000000)
  directionHi := (106114121709139082259/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree014.table
  base := (-238214937217465841673236200551718513711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-7963027450384336375366345200000000000000)
      constant := (-1414789574597280380548430693103110822660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree014.table
  base := (-309783206218937835632180211607564246033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-36985428915125567461696930860000000000000)
      constant := (-4916189666826163559975896107233877143128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53057060854569541129/50000000000000000000)
  centralHi := (106114121709139082259/100000000000000000000)
  directionLo := (110119828286989173363/100000000000000000000)
  directionHi := (27529957071747293341/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree015.table
  base := (-137843684677896143727672236494011677419/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-141708813950059815608972788140000000000000)
      constant := (-17771323412604563558843250253262887741240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree015.table
  base := (-2836197920842472662821818530611684035519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-219282085690733370419991384060000000000000)
      constant := (-12612568754984289580772337999917553221293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110119828286989173363/100000000000000000000)
  centralHi := (27529957071747293341/25000000000000000000)
  directionLo := (113984851352317776031/100000000000000000000)
  directionHi := (3562026604759930501/3125000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree016.table
  base := (-1540432777565937952117472621053857971033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-460064538631526411260885814040000000000000)
      constant := (-11573735323149022413111683259668486967404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree016.table
  base := (-62939277047197882065618274865919381699/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-2134791525592047861936695300940000000000000)
      constant := (127459473935949684508621191219432900611150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113984851352317776031/100000000000000000000)
  centralHi := (3562026604759930501/3125000000000000000)
  directionLo := (29430762067163647193/25000000000000000000)
  directionHi := (117723048268654588773/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree017.table
  base := (-105197104119037669279765358479468753849/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-495002635412873375694853263660000000000000)
      constant := (52314397364397020257746487370157963788608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree017.table
  base := (-42774225686971324052580595388611629969/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-2296044279967495390093468145340000000000000)
      constant := (466975874622781669555911833269345084081040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/25000000000000000000)
  centralHi := (117723048268654588773/100000000000000000000)
  directionLo := (121346140645337282217/100000000000000000000)
  directionHi := (60673070322668641109/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree018.table
  base := (-905485019406728818971246960444430411093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-176646910731406780042940237760000000000000)
      constant := (45260185979315100520482286805783278851544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree018.table
  base := (-733845412190094150230187941415195772703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-273033003815882546472248998860000000000000)
      constant := (99367904557052332812104174259831107063295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121346140645337282217/100000000000000000000)
  centralHi := (60673070322668641109/50000000000000000000)
  directionLo := (12486414859907536903/10000000000000000000)
  directionHi := (124864148599075369031/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree019.table
  base := (-385408208315028419487443365292274824807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-564878828975567304562788162900000000000000)
      constant := (236967168971303879628441641825712015067420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree019.table
  base := (-1947328814484226829152776167527538396411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-2618549788718390446407013834140000000000000)
      constant := (1401756471440176968612790589122133403096494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12486414859907536903/10000000000000000000)
  centralHi := (124864148599075369031/100000000000000000000)
  directionLo := (128285717682156551429/100000000000000000000)
  directionHi := (12828571768215655143/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree020.table
  base := (-4067339772040182440187926945406137632407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-599816925756914268996755612520000000000000)
      constant := (354519941908176896176204007650595536072342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree020.table
  base := (-4102459369595482491782392697991415626531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-2779802543093837974563786678540000000000000)
      constant := (1983716091100495349061153092557357126099487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128285717682156551429/100000000000000000000)
  centralHi := (12828571768215655143/10000000000000000000)
  directionLo := (131618369223600292691/100000000000000000000)
  directionHi := (32904592305900073173/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree021.table
  base := (-53313808083914227581843972733790330011/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (-4318061377811300907691993620000000000000)
      constant := (3315930442436088856846606997593547198240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree021.table
  base := (-4295737121471780273850624377507623984597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (-6669059631449626990296053340000000000000)
      constant := (5977510880892088612680094467477128046209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131618369223600292691/100000000000000000000)
  centralHi := (32904592305900073173/25000000000000000000)
  directionLo := (26973738986602484991/20000000000000000000)
  directionHi := (33717173733253106239/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree022.table
  base := (-222495067857127184285701664375583995863/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-669693119319608197864690511760000000000000)
      constant := (634990421268911072591500162491566104325560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree022.table
  base := (-895359721188535576987588052803361908037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-3102308051844733030877332367340000000000000)
      constant := (3355801978219051401199258597905760978335245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26973738986602484991/20000000000000000000)
  centralHi := (33717173733253106239/25000000000000000000)
  directionLo := (5521700408937517861/4000000000000000000)
  directionHi := (69021255111718973263/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree023.table
  base := (-462363209118775934238571345559250881757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-704631216100955162298657961380000000000000)
      constant := (796606637369942951460068218680802407634420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree023.table
  base := (-2323691184169681285082351281462102956713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-3263560806220180559034105211740000000000000)
      constant := (4140575034864255592788924708051275576537402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5521700408937517861/4000000000000000000)
  centralHi := (69021255111718973263/50000000000000000000)
  directionLo := (14114497647681963683/10000000000000000000)
  directionHi := (141144976476819636831/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree024.table
  base := (-4787748689091939341636904685688599162793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-246523104294100708910875137000000000000000)
      constant := (323954527436571124676765855522517282046286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree024.table
  base := (-4808816931181392606352449424335162741969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-380534840066180898576764228460000000000000)
      constant := (554293759235072005858447224222731076930557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14114497647681963683/10000000000000000000)
  centralHi := (141144976476819636831/100000000000000000000)
  directionLo := (72090349805809597099/50000000000000000000)
  directionHi := (144180699611619194199/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree025.table
  base := (-2471687154205854486207986432925718463193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-774507409663649091166592860620000000000000)
      constant := (1160431047766574505351368635064677543642516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree025.table
  base := (-4962132418556634393742096437186193092203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-3586066314971075615347650900540000000000000)
      constant := (5898645518804981533491828203602666539015431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/50000000000000000000)
  centralHi := (144180699611619194199/100000000000000000000)
  directionLo := (29430762067163647193/20000000000000000000)
  directionHi := (73576905167909117983/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree026.table
  base := (-1018277963468813250910869910771773171763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-809445506444996055600560310240000000000000)
      constant := (1362050058490608927592840546185493437508390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree026.table
  base := (-638517409418572001288714461097706731779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-3747319069346523143504423744940000000000000)
      constant := (6869507873351401307923990893341871950851064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/20000000000000000000)
  centralHi := (73576905167909117983/50000000000000000000)
  directionLo := (150068030080373762891/100000000000000000000)
  directionHi := (37517007520093440723/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree027.table
  base := (-5232495478094643964122528651753664870713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-281461201075447673344842586620000000000000)
      constant := (525504912464453534863329364243140842670126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree027.table
  base := (-2623742074355232080488055949946202165247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-434285758191330074629021843260000000000000)
      constant := (877819486952351331712476493515816563417382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150068030080373762891/100000000000000000000)
  centralHi := (37517007520093440723/25000000000000000000)
  directionLo := (152926725617394826779/100000000000000000000)
  directionHi := (7646336280869741339/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree028.table
  base := (-5367255275769316109353289307630719683587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-17945340816483469070785616520000000000000)
      constant := (36809372915381685263721922554215681898478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree028.table
  base := (-107613797394025843213538480936773866003/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-83057644450967718363632029260000000000000)
      constant := (183480741652514600210140213935355280895950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152926725617394826779/100000000000000000000)
  centralHi := (7646336280869741339/5000000000000000000)
  directionLo := (155732954649656479827/100000000000000000000)
  directionHi := (38933238662414119957/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree029.table
  base := (-5496129020798628217247859421170362422743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-914259796789036948902462659100000000000000)
      constant := (2043348480605054462651637880960913447713558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree029.table
  base := (-5508184322639593692676493797431223363389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-4231077332472865727974742278140000000000000)
      constant := (10139484657604141519619012990398491490236353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155732954649656479827/100000000000000000000)
  centralHi := (38933238662414119957/25000000000000000000)
  directionLo := (79244752065619399657/50000000000000000000)
  directionHi := (31697900826247759863/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree030.table
  base := (-5619495804736941440432337151714656328669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-316399297856794637778810036240000000000000)
      constant := (765156969243478026635235420431963679790438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree030.table
  base := (-1407580377845972151551912321791242351431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-488036676316479250681279458060000000000000)
      constant := (1260743553928790950315964926786749497358572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79244752065619399657/50000000000000000000)
  centralHi := (31697900826247759863/20000000000000000000)
  directionLo := (6447956907501160907/4000000000000000000)
  directionHi := (40299730671882255669/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree031.table
  base := (-5737671312679903161339253523013615932173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-984135990351730877770397558340000000000000)
      constant := (2559933742811721099249415225178996915941138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree031.table
  base := (-5747397114716238892323546492322826883477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-4553582841223760784288287966940000000000000)
      constant := (12611787141209478495807559178256900033159929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6447956907501160907/4000000000000000000)
  centralHi := (40299730671882255669/25000000000000000000)
  directionLo := (40965887052120845741/25000000000000000000)
  directionHi := (32772709641696676593/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree032.table
  base := (-5850920746368676579086916838752016553129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1019074087133077842204365007960000000000000)
      constant := (2836659016537013540141982131326907133380074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree032.table
  base := (-5859660122730451684635890511897187731769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-4714835595599208312445060811340000000000000)
      constant := (13934440711261114510742351655960020630869613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40965887052120845741/25000000000000000000)
  centralHi := (32772709641696676593/20000000000000000000)
  directionLo := (83242765732716912687/50000000000000000000)
  directionHi := (1331884251723470603/800000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree033.table
  base := (-2979734295135182350743537646310766422303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-351337394638141602212777485860000000000000)
      constant := (1041860243490994372762251003598089781228612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree033.table
  base := (-5967321663422178346948884836831128986691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-541787594441628426733537072860000000000000)
      constant := (1701597041463975538148344506185824038956423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83242765732716912687/50000000000000000000)
  centralHi := (1331884251723470603/800000000000000000)
  directionLo := (42266714107544156077/25000000000000000000)
  directionHi := (169066856430176624309/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree034.table
  base := (-6063506089124574981037014494713725329989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1088950280695771771072299907200000000000000)
      constant := (3426642658666185242649525894214164752983234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree034.table
  base := (-3035280897740369308877251860252220331693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-5037341104350103368758606500140000000000000)
      constant := (16751346909307504479560923940172625002340322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42266714107544156077/25000000000000000000)
  centralHi := (169066856430176624309/100000000000000000000)
  directionLo := (85804678921134530421/50000000000000000000)
  directionHi := (171609357842269060843/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree035.table
  base := (-6163197051447010676614733564857601255607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-22936497499533035418495252180000000000000)
      constant := (76322380437000064390207531435854392466358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree035.table
  base := (-6169534812878283240247009044993507189841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-106093752218888793814599578460000000000000)
      constant := (372350146708798632370894149785175305874293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85804678921134530421/50000000000000000000)
  centralHi := (171609357842269060843/100000000000000000000)
  directionLo := (87057368233380958679/50000000000000000000)
  directionHi := (174114736466761917359/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree036.table
  base := (-6258682415838311636714316774673017433377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-386275491419488566646744935480000000000000)
      constant := (1355000414254949580080473891122044291529054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree036.table
  base := (-6264373447173725498966338083993131924129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-595538512566777602785794687660000000000000)
      constant := (2199514289732691454191936860053009607153037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87057368233380958679/50000000000000000000)
  centralHi := (174114736466761917359/100000000000000000000)
  directionLo := (88292286201490941579/50000000000000000000)
  directionHi := (176584572402981883159/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree037.table
  base := (-6350083892439887169356182663315609235153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1193764571039812664374202256060000000000000)
      constant := (4402220679940147661455280742730210884865018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree037.table
  base := (-1588798060619464434006547326736395227503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-5521099367476445953228925033340000000000000)
      constant := (21402609624038196515605356068110996456054124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88292286201490941579/50000000000000000000)
  centralHi := (176584572402981883159/100000000000000000000)
  directionLo := (35804067348053041847/20000000000000000000)
  directionHi := (44755084185066302309/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree038.table
  base := (-643750690438211372342170402845149795481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1228702667821159628808169705680000000000000)
      constant := (4751423958538569242790622645935259601285860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree038.table
  base := (-1610522575159413924277308263226187779983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-5682352121851893481385697877740000000000000)
      constant := (23065969126319504358269413463807014268329964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35804067348053041847/20000000000000000000)
  centralHi := (44755084185066302309/25000000000000000000)
  directionLo := (90711700902435883269/50000000000000000000)
  directionHi := (181423401804871766539/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree039.table
  base := (-6521042992380859087851760960805557338823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-421213588200835531080712385100000000000000)
      constant := (1704194721863216118099609545436055380795346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree039.table
  base := (-3262576769999123826031639417481108368551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-649289430691926778838052302460000000000000)
      constant := (2753954827163060212745661326860554139646006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90711700902435883269/50000000000000000000)
  centralHi := (181423401804871766539/100000000000000000000)
  directionLo := (183795050200776481063/100000000000000000000)
  directionHi := (22974381275097060133/12500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree040.table
  base := (-1320154360393862936286777804344188999769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1298578861383853557676104604920000000000000)
      constant := (5485677885306626718856363258814042170339570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree040.table
  base := (-1320891314588701968694440167373769762807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-6004857630602788537699243566540000000000000)
      constant := (26561383866298440915991505956822513019031695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183795050200776481063/100000000000000000000)
  centralHi := (22974381275097060133/12500000000000000000)
  directionLo := (186136482813445106279/100000000000000000000)
  directionHi := (4653412070336127657/2500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree041.table
  base := (-3338381370894316076250570442348109267801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1333516958165200522110072054540000000000000)
      constant := (5870684711549005751853309027444311750533012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree041.table
  base := (-3340032140191348396226879972242033197899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-6166110384978236065856016410940000000000000)
      constant := (28393254554369257630672277857047580158359246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186136482813445106279/100000000000000000000)
  centralHi := (4653412070336127657/2500000000000000000)
  directionLo := (18844882591837483789/10000000000000000000)
  directionHi := (188448825918374837891/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree042.table
  base := (-1687269094783620056044322842428255776107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (-9309218060860867255401629280000000000000)
      constant := (42636645153277951351641334320573953791144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree042.table
  base := (-1350406628410664665925389315802341873243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (-14347762220756652140618569740000000000000)
      constant := (68664695659835056548399871462964871901355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18844882591837483789/10000000000000000000)
  centralHi := (188448825918374837891/100000000000000000000)
  directionLo := (47683284378456423801/25000000000000000000)
  directionHi := (38146627502765139041/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree043.table
  base := (-6817765622942448955741831194074721474379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1403393151727894450978006953780000000000000)
      constant := (6676368708028122531942094340967031886532574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree043.table
  base := (-3410206183806688456634900148446243505883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-6488615893729131122169562099740000000000000)
      constant := (32224947456774930430205855998011239683433582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47683284378456423801/25000000000000000000)
  centralHi := (38146627502765139041/20000000000000000000)
  directionLo := (192990412978784884859/100000000000000000000)
  directionHi := (9649520648939244243/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree044.table
  base := (-6882876732762709191196677702749021438781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1438331248509241415411974403400000000000000)
      constant := (7097016722730046573469199915551787696998386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree044.table
  base := (-6885244863385051986999652449736688543873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-6649868648104578650326334944140000000000000)
      constant := (34224647801668005858851086527398361056456021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192990412978784884859/100000000000000000000)
  centralHi := (9649520648939244243/5000000000000000000)
  directionLo := (19522159014201257133/10000000000000000000)
  directionHi := (195221590142012571331/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree045.table
  base := (-6944450183745091442657627893173319597413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-491089781763529459948647284340000000000000)
      constant := (2509839660647860267570182850544014679453526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree045.table
  base := (-6946568062170619843306051779493716661369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-756791266942225130942567532060000000000000)
      constant := (4031131366341009033757373546414423650778757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19522159014201257133/10000000000000000000)
  centralHi := (195221590142012571331/100000000000000000000)
  directionLo := (49356888458850109759/25000000000000000000)
  directionHi := (197427553835400439037/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree046.table
  base := (-7002521411335359346749245525847250113681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1508207442071935344279909302640000000000000)
      constant := (7973865067647670710498518503620908466577786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree046.table
  base := (-7004414638013795084494159052574312707991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-6972374156855473706639880632940000000000000)
      constant := (38391507715218322346251954475044184287327907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49356888458850109759/25000000000000000000)
  centralHi := (197427553835400439037/100000000000000000000)
  directionLo := (4990228499858745023/2500000000000000000)
  directionHi := (199609139994349800921/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree047.table
  base := (-1764280363661181083710683544046213160901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1543145538853282308713876752260000000000000)
      constant := (8430045854343620136009975920346653322780424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree047.table
  base := (-352940656179382311457474680535054910399/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-7133626911230921234796653477340000000000000)
      constant := (40558586307389259336069222110242447070842460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4990228499858745023/2500000000000000000)
  centralHi := (199609139994349800921/100000000000000000000)
  directionLo := (201767139359059001051/100000000000000000000)
  directionHi := (50441784839764750263/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree048.table
  base := (-3554138756928270109223859520173889153249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-526027878544876424382614733960000000000000)
      constant := (2966017781725841019553696998045917725963196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree048.table
  base := (-7109788444675864477742062392347348320097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-810542185067374306994825146860000000000000)
      constant := (4753487232974452090560705071524939796945741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201767139359059001051/100000000000000000000)
  centralHi := (50441784839764750263/25000000000000000000)
  directionLo := (50975575205798275593/25000000000000000000)
  directionHi := (203902300823193102373/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree049.table
  base := (-7156013434265419717566509015846955008673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-32918810865632168113914523500000000000000)
      constant := (191385316931280884464718059369918269947962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree049.table
  base := (-1789340595928375238617179618779587404007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-152165967754730944716534676860000000000000)
      constant := (919589291126513839711650784771804560367244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/25000000000000000000)
  centralHi := (203902300823193102373/100000000000000000000)
  directionLo := (206015334470145530351/100000000000000000000)
  directionHi := (12875958404384095647/6250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree050.table
  base := (-3600175063692102176691360992870694821149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1647959829197323202015779101120000000000000)
      constant := (9869521259724565569112274007692031445164388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree050.table
  base := (-7201553982379328006629908721400681818759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-7617385174357263819266972010540000000000000)
      constant := (47394031620535571513064359341586897953781843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206015334470145530351/100000000000000000000)
  centralHi := (12875958404384095647/6250000000000000000)
  directionLo := (208106914331792281717/100000000000000000000)
  directionHi := (104053457165896140859/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree051.table
  base := (-7241305937846228642968017202660239808929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-560965975326223388816582183580000000000000)
      constant := (3457656714043576467221763489854296498724958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree051.table
  base := (-7242379891651987388244714633353365090803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-864293103192523483047082761660000000000000)
      constant := (5531536903726056208451057053297055331651959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208106914331792281717/100000000000000000000)
  centralHi := (104053457165896140859/50000000000000000000)
  directionLo := (105088840450061502261/50000000000000000000)
  directionHi := (210177680900123004523/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree052.table
  base := (-3639448481730797139683563938795201799491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1717836022760017130883714000360000000000000)
      constant := (10888222444095084938675082730708421341899292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree052.table
  base := (-7279854676460880415085650302575947631323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-7939890683108158875580517699340000000000000)
      constant := (52229257534794383294089314724892021283759671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105088840450061502261/50000000000000000000)
  centralHi := (210177680900123004523/100000000000000000000)
  directionLo := (53057060854569541129/25000000000000000000)
  directionHi := (212228243418278164517/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree053.table
  base := (-7313137334675465581075360520653303601129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1752774119541364095317681449980000000000000)
      constant := (11415274011266753870504030677152928741268074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree053.table
  base := (-3656995540505729730319583273721399413853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-8101143437483606403737290543740000000000000)
      constant := (54730290963731390277031188644533177150944962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53057060854569541129/25000000000000000000)
  centralHi := (212228243418278164517/100000000000000000000)
  directionLo := (214259181974220016603/100000000000000000000)
  directionHi := (53564795493555004151/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree054.table
  base := (-1468807891752914503983370330546092295537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-595904072107570353250549633200000000000000)
      constant := (3984707065302125861811946057252414775186870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree054.table
  base := (-1468960051998562344596081081611610278029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-918044021317672659099340376460000000000000)
      constant := (6365213073632429384647969146615466445648685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214259181974220016603/100000000000000000000)
  centralHi := (53564795493555004151/25000000000000000000)
  directionLo := (216271049417428791297/100000000000000000000)
  directionHi := (108135524708714395649/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree055.table
  base := (-1842903558337922828082056108266018720423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1822650313104058024185616349220000000000000)
      constant := (12504760794112859875838138005704161984782552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree055.table
  base := (-7372291980145873628604790544387319989191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-8423648946234501460050836232540000000000000)
      constant := (59899124710277546956237470247775575654300307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216271049417428791297/100000000000000000000)
  centralHi := (108135524708714395649/50000000000000000000)
  directionLo := (218264373116571466177/100000000000000000000)
  directionHi := (109132186558285733089/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree056.table
  base := (-7395871233184562633632361114203752142141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-37909967548681734461624159160000000000000)
      constant := (266677346753272754758489852994777487147154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree056.table
  base := (-1479294959211055497023888686184673924833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-175202075522652020167502226060000000000000)
      constant := (1276875526301489167699677769765069020147545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218264373116571466177/100000000000000000000)
  centralHi := (109132186558285733089/50000000000000000000)
  directionLo := (220239656573978346727/100000000000000000000)
  directionHi := (27529957071747293341/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree057.table
  base := (-7416818873591211554073921401759155535183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-630842168888917317684517082820000000000000)
      constant := (4547135437397484512255834197142602757552066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree057.table
  base := (-1854339050876349906205826715362716809089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-971794939442821835151597991260000000000000)
      constant := (7254470664583933484148938046166722516255668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220239656573978346727/100000000000000000000)
  centralHi := (27529957071747293341/12500000000000000000)
  directionLo := (222197380910932256277/100000000000000000000)
  directionHi := (111098690455466128139/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree058.table
  base := (-7434464553569445977541353072365727444849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1927464603448098917487518698080000000000000)
      constant := (14227407582653770012899433743424476131214394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree058.table
  base := (-7434942773295192269626602649219420512907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-8907407209360844044521154765740000000000000)
      constant := (68069121594557829586818941879882706661424039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222197380910932256277/100000000000000000000)
  centralHi := (111098690455466128139/50000000000000000000)
  directionLo := (22413800623618458713/10000000000000000000)
  directionHi := (224138006236184587131/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree059.table
  base := (-1862203695270035930324386296893599040677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-1962402700229445881921486147700000000000000)
      constant := (14825191888953816333286506868638127528163848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree059.table
  base := (-465577516751496295400192600015149624497/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-9068659963736291572677927610140000000000000)
      constant := (70903550004761399444725736795279312748647504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22413800623618458713/10000000000000000000)
  centralHi := (224138006236184587131/100000000000000000000)
  directionLo := (11303098645436338877/5000000000000000000)
  directionHi := (226061972908726777541/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree060.table
  base := (-1864968820695152062188148603485731296213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-665780265670264282118484532440000000000000)
      constant := (5144919182485115093228717849033593331884504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree060.table
  base := (-7460253744030939073257797262809096229433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1025545857567971011203855606060000000000000)
      constant := (8199279391369913873969760146367062854273349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11303098645436338877/5000000000000000000)
  centralHi := (226061972908726777541/100000000000000000000)
  directionLo := (227969702704635552063/100000000000000000000)
  directionHi := (3562026604759930501/1562500000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree061.table
  base := (-3733825550073452472932583183276111349817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2032278893792139810789421046940000000000000)
      constant := (16056103075964393628626526087978646526307604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree061.table
  base := (-1493597528077591715404123691829407088301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-9391165472487186628991473298940000000000000)
      constant := (76739009274369352463809338994148472110888885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227969702704635552063/100000000000000000000)
  centralHi := (3562026604759930501/1562500000000000000)
  directionLo := (57465399974187683353/25000000000000000000)
  directionHi := (229861599896750733413/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree062.table
  base := (-7472146673685548833020306613035316351891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2067216990573486775223388496560000000000000)
      constant := (16689227168972045964114421094387616992544046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree062.table
  base := (-373622292829877617606740613211814410637/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-9552418226862634157148246143340000000000000)
      constant := (79740029101839904468561787485615390694544980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57465399974187683353/25000000000000000000)
  centralHi := (229861599896750733413/100000000000000000000)
  directionLo := (46347610451002936431/20000000000000000000)
  directionHi := (57934513063753670539/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree063.table
  base := (-7473365916719393237435083448905292102967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (-14300374743910433603111264940000000000000)
      constant := (117919242693614853115292656377189415794066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree063.table
  base := (-3736815910218567568174783827005479316509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (-22026464810063677290941086140000000000000)
      constant := (187747323060751385900097527837967124100946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46347610451002936431/20000000000000000000)
  centralHi := (57934513063753670539/25000000000000000000)
  directionLo := (11679971598724235987/5000000000000000000)
  directionHi := (233599431974484719741/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree064.table
  base := (-3735656140022643180368363298399997394943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2137093184136180704091323395800000000000000)
      constant := (17990806582398132588848918728700801531773516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree064.table
  base := (-7471548547203763963062617130584122514223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-9874923735613529213461791832140000000000000)
      constant := (85908626388985716148767805766637205913682971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11679971598724235987/5000000000000000000)
  centralHi := (233599431974484719741/100000000000000000000)
  directionLo := (29430762067163647193/12500000000000000000)
  directionHi := (47089219307461835509/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree065.table
  base := (-7465988808598043010977243753818690959107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2172031280917527668525290845420000000000000)
      constant := (18659259993071457953249825555202304858022542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree065.table
  base := (-3733099345726864666407317471765913276369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-10036176489988976741618564676540000000000000)
      constant := (89076196347444997036820863423707393470727626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29430762067163647193/12500000000000000000)
  centralHi := (47089219307461835509/20000000000000000000)
  directionLo := (949113558057284619/400000000000000000)
  directionHi := (237278389514321154751/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree066.table
  base := (-7457398191113186021540332259873949576343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-735656459232958210986419431680000000000000)
      constant := (6446496039164371929378644649672352941518386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree066.table
  base := (-3728792296095575388432031247990521488563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1133047693818269363308370835660000000000000)
      constant := (10255475138962972634027473863490786682362478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (949113558057284619/400000000000000000)
  centralHi := (237278389514321154751/100000000000000000000)
  directionLo := (119548320655670347601/50000000000000000000)
  directionHi := (239096641311340695203/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree067.table
  base := (-148910856073138505907722746333424549249/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2241907474480221597393225744660000000000000)
      constant := (20031490257099640382036961220843659126039700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree067.table
  base := (-3722854156168974248969831121446894073727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-10358681998739871797932110365340000000000000)
      constant := (95577863369405285728836857081851518280918358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119548320655670347601/50000000000000000000)
  centralHi := (239096641311340695203/100000000000000000000)
  directionLo := (240901169864776515143/100000000000000000000)
  directionHi := (30112646233097064393/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree068.table
  base := (-928803093472945157464977879826798641641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2276845571261568561827193194280000000000000)
      constant := (20735265794034067409354589121047369594860368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree068.table
  base := (-7430571673211432027046795025394482881529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-10519934753115319326088883209740000000000000)
      constant := (98911955294057792595069547962203099147737133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240901169864776515143/100000000000000000000)
  centralHi := (30112646233097064393/12500000000000000000)
  directionLo := (121346140645337282217/50000000000000000000)
  directionHi := (48538456258134912887/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree069.table
  base := (-7412045883985869306941302324449785970783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-770594556014305175420386881300000000000000)
      constant := (7150271393770506968241081085798920974863266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree069.table
  base := (-148243525692864873706321108919890363189/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1186798611943418539360628450460000000000000)
      constant := (11366838877201890168232173417038805830560850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121346140645337282217/50000000000000000000)
  centralHi := (48538456258134912887/20000000000000000000)
  directionLo := (244470270490965640979/100000000000000000000)
  directionHi := (12223513524548282049/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree070.table
  base := (-923800982627659542642134363342304638247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-47892280914780867157043430480000000000000)
      constant := (452614998657088109353908014459569377364144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree070.table
  base := (-1478104714258547992455085537665476425347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-221274291058494171069437324460000000000000)
      constant := (2158094801772624772454109640415160682578155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244470270490965640979/100000000000000000000)
  centralHi := (12223513524548282049/5000000000000000000)
  directionLo := (61558855430078002963/25000000000000000000)
  directionHi := (246235421720312011853/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree071.table
  base := (-92068901770303197622065155312377299127/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2381659861605609455129095543140000000000000)
      constant := (22917227622647521576656664412397885924532960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree071.table
  base := (-7365614795637549999059933681142243807163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-11003693016241661910559201742940000000000000)
      constant := (109247239799924696249833348831448811443123351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61558855430078002963/25000000000000000000)
  centralHi := (246235421720312011853/100000000000000000000)
  directionLo := (123994004558319172723/50000000000000000000)
  directionHi := (247988009116638345447/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree072.table
  base := (-29349440100208097933485378770008359857/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-805532652795652139854354330920000000000000)
      constant := (7889363954893503943042781067974795183503500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree072.table
  base := (-733745107806268532242416289934789559363/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1240549530068567715412886065260000000000000)
      constant := (12533703550193987606993240914595859347736390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123994004558319172723/50000000000000000000)
  centralHi := (247988009116638345447/100000000000000000000)
  directionLo := (249728297198150738061/100000000000000000000)
  directionHi := (124864148599075369031/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree073.table
  base := (-28538877604903039912028512701989179979/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2451536055168303383997030442380000000000000)
      constant := (24430727320564412934232523785622486358060544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree073.table
  base := (-182650835360400832154671667291352084443/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-11326198524992556966872747431740000000000000)
      constant := (116414920424815435520466622545741647691276440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249728297198150738061/100000000000000000000)
  centralHi := (124864148599075369031/50000000000000000000)
  directionLo := (62864135332348831849/25000000000000000000)
  directionHi := (251456541329395327397/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree074.table
  base := (-1817822774054089983955508013924407944479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2486474151949650348430997892000000000000000)
      constant := (25205133687719527872391717107284896257292696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree074.table
  base := (-3635681345675672237036674489702884494413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-11487451279368004495029520276140000000000000)
      constant := (120082004046090425400147134686646167627783202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62864135332348831849/25000000000000000000)
  centralHi := (251456541329395327397/100000000000000000000)
  directionLo := (253172988158681531649/100000000000000000000)
  directionHi := (5063459763173630633/2000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree075.table
  base := (-7233376231157544632120325901923660237773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-840470749576999104288321780540000000000000)
      constant := (8663770232082465331817337675486481296698246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree075.table
  base := (-7233439699739048569043341734178105639393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1294300448193716891465143680060000000000000)
      constant := (13756064641027697736824997695075818471009229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253172988158681531649/100000000000000000000)
  centralHi := (5063459763173630633/2000000000000000000)
  directionLo := (50975575205798275593/20000000000000000000)
  directionHi := (127438938014495688983/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree076.table
  base := (-3596104445939648906073550658258105821897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2556350345512344277298932791240000000000000)
      constant := (26789258105009051044716172908464233776724564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree076.table
  base := (-7192265146389644015445997644534571540077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-11809956788118899551343065964940000000000000)
      constant := (127582652659181708772426227245880761852478129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975575205798275593/20000000000000000000)
  centralHi := (127438938014495688983/50000000000000000000)
  directionLo := (256571435364313102859/100000000000000000000)
  directionHi := (12828571768215655143/5000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree077.table
  base := (-7147789812462756105747715698049599351727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-52883437597830433504753066140000000000000)
      constant := (563244402003768139816523707716702403889638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree077.table
  base := (-7147839664303342358344717912570455987589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-244310398826415246520404873660000000000000)
      constant := (2681963589355682305082285691160597688335097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256571435364313102859/100000000000000000000)
  centralHi := (12828571768215655143/5000000000000000000)
  directionLo := (258253889033171957281/100000000000000000000)
  directionHi := (129126944516585978641/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree078.table
  base := (-1775029912784128949210381080430706968841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-875408846358346068722289230160000000000000)
      constant := (9473487760751650702286729628171162868214328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree078.table
  base := (-7100163821632531706197928312608408452157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1348051366318866067517401294860000000000000)
      constant := (15033918963924871410416866313246563957532921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258253889033171957281/100000000000000000000)
  centralHi := (129126944516585978641/50000000000000000000)
  directionLo := (129962726345490972837/50000000000000000000)
  directionHi := (10397018107639277827/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree079.table
  base := (-7049198999285593309201820286473436961063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2661164635856385170600835140100000000000000)
      constant := (29253720683352795983678406356561809533447478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree079.table
  base := (-7049238129519952550115813126568188352259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-12293715051245242135813384498140000000000000)
      constant := (139249816373626092336846847297950286809961343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129962726345490972837/50000000000000000000)
  centralHi := (10397018107639277827/4000000000000000000)
  directionLo := (52317267020541465673/20000000000000000000)
  directionHi := (130793167551353664183/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree080.table
  base := (-3497514194678850490780621744888027441143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2696102732637732135034802589720000000000000)
      constant := (30098747744938543053876917964405839864607916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree080.table
  base := (-3497531524477407368885944869484533690707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-12454967805620689663970157342540000000000000)
      constant := (143249852363446457249845086803343923854389278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52317267020541465673/20000000000000000000)
  centralHi := (130793167551353664183/50000000000000000000)
  directionLo := (131618369223600292691/50000000000000000000)
  directionHi := (263236738447200585383/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree081.table
  base := (-693760830180287659200716836083957484281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-910346943139693033156256679780000000000000)
      constant := (10318514775253294070232678541952721665404620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree081.table
  base := (-3468819498385522150157221000368770990163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1401802284444015243569658909660000000000000)
      constant := (16367264232590405921504148422291581328892078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131618369223600292691/50000000000000000000)
  centralHi := (263236738447200585383/100000000000000000000)
  directionLo := (264876858604472824737/100000000000000000000)
  directionHi := (132438429302236412369/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree082.table
  base := (-1375387834233135792250994399463186153071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2765978926200426063902737488960000000000000)
      constant := (31824110298060713160851438474209116354985630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree082.table
  base := (-3438483175448049704723364494171993187929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-12777473314371584720283703031340000000000000)
      constant := (151416393063229653306760182531620906024739866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264876858604472824737/100000000000000000000)
  centralHi := (132438429302236412369/50000000000000000000)
  directionLo := (266506885427052124647/100000000000000000000)
  directionHi := (33313360678381515581/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree083.table
  base := (-6813021391434419499409720313310087926683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2800917022981773028336704938580000000000000)
      constant := (32704445546008472349766237130711834149555198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree083.table
  base := (-6813045454945044860729136456420614852177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-12938726068747032248440475875740000000000000)
      constant := (155582896818591726564987236642955526550569829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266506885427052124647/100000000000000000000)
  centralHi := (33313360678381515581/12500000000000000000)
  directionLo := (268127002996493970737/100000000000000000000)
  directionHi := (134063501498246985369/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree084.table
  base := (-6745855320738982405092708382658984403103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (-19291531426959999950820900600000000000000)
      constant := (228547958940904583830256944514682031193794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree084.table
  base := (-210808644445080314652492625096171690267/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (-29705167399370702441263602540000000000000)
      constant := (362369362686783013543189234390767517734368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268127002996493970737/100000000000000000000)
  centralHi := (134063501498246985369/50000000000000000000)
  directionLo := (269737389866024849911/100000000000000000000)
  directionHi := (33717173733253106239/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree085.table
  base := (-6675441285477468139505407480822710753099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2870793216544466957204639837820000000000000)
      constant := (34500423457013176045102807058063123038588894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree085.table
  base := (-267018405573806195259237136498149595649/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-13261231577497927304754021564540000000000000)
      constant := (164082369062954177691086424596323702123909325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269737389866024849911/100000000000000000000)
  centralHi := (33717173733253106239/12500000000000000000)
  directionLo := (67834554822556090481/25000000000000000000)
  directionHi := (10853528771608974477/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree086.table
  base := (-6601779583941977640071321000297729385609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2905731313325813921638607287440000000000000)
      constant := (35416065936411201340328835776532467560630954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree086.table
  base := (-3300898134563218515097238042049065139883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-13422484331873374832910794408940000000000000)
      constant := (168415336825058510001618530546338173639869582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67834554822556090481/25000000000000000000)
  centralHi := (10853528771608974477/4000000000000000000)
  directionLo := (272929659442582169997/100000000000000000000)
  directionHi := (136464829721291084999/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree087.table
  base := (-326243524475258247973768173993024921349/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-980223136702386962024191579020000000000000)
      constant := (12114492440711829805745497374888671154155960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree087.table
  base := (-260995410139233832376622729726202192119/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1509304120694313595674174139260000000000000)
      constant := (19200421323461997327517552435056206943962675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272929659442582169997/100000000000000000000)
  centralHi := (136464829721291084999/50000000000000000000)
  directionLo := (10980474944868123057/4000000000000000000)
  directionHi := (137255936810851538213/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree088.table
  base := (-161117856335539289874437092571778929371/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-2975607506888507850506542186680000000000000)
      constant := (37282657540317205075631351160155879790597040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree088.table
  base := (-3222363657846795568943070319659695549927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-13744989840624269889224340097740000000000000)
      constant := (177247734025846242806709167706980445574893158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10980474944868123057/4000000000000000000)
  centralHi := (137255936810851538213/50000000000000000000)
  directionLo := (276085020446875893051/100000000000000000000)
  directionHi := (69021255111718973263/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree089.table
  base := (-3180655553645541768830430352084608219953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3010545603669854814940509636300000000000000)
      constant := (38233606522865981834134958246759250366667636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree089.table
  base := (-3180661331259503396411481130874678820431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-13906242594999717417381112942140000000000000)
      constant := (181747162895587326991514332548105599841139574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276085020446875893051/100000000000000000000)
  centralHi := (69021255111718973263/25000000000000000000)
  directionLo := (277649254043669057679/100000000000000000000)
  directionHi := (3470615675545863221/1250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree090.table
  base := (-392166329076625334758611522986022502237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1015161233483733926458159028640000000000000)
      constant := (13065441402277600716525100052857916716492384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree090.table
  base := (-3137335743001964467846705957138466018081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1563055038819462771726431754060000000000000)
      constant := (20700230918478140473383569364601290990684186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277649254043669057679/100000000000000000000)
  centralHi := (3470615675545863221/1250000000000000000)
  directionLo := (279204724220167659419/100000000000000000000)
  directionHi := (13960236211008382971/5000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree091.table
  base := (-1546191231439530556307885455551243456257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-62865750963929566200172337460000000000000)
      constant := (819812459874475942460292458771770157049832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree091.table
  base := (-618477396508814797488644281068926605539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-290382614362257397422339972060000000000000)
      constant := (3896173059209320651086203220511389816504470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279204724220167659419/100000000000000000000)
  centralHi := (13960236211008382971/5000000000000000000)
  directionLo := (280751576634422261347/100000000000000000000)
  directionHi := (70187894158605565337/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree092.table
  base := (-6091622273517631170678547176246641504361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3115359894013895708242411985160000000000000)
      constant := (41157065449634261001505543462503487397717866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree092.table
  base := (-6091630267009917693308672866514446680269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-14390000858126060001851431475340000000000000)
      constant := (195578367579191460165044377616801387042004113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280751576634422261347/100000000000000000000)
  centralHi := (70187894158605565337/25000000000000000000)
  directionLo := (282289952953639273661/100000000000000000000)
  directionHi := (141144976476819636831/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree093.table
  base := (-5995233480711888471510531945183680685447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1050099330265080890892126478260000000000000)
      constant := (14051696301186219622131203347046999292826194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree093.table
  base := (-5995240548540965644699237042977298181937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1616805956944611947778689368860000000000000)
      constant := (22255526788077612610257389795882337167255261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282289952953639273661/100000000000000000000)
  centralHi := (141144976476819636831/50000000000000000000)
  directionLo := (283819991005605299521/100000000000000000000)
  directionHi := (141909995502802649761/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree094.table
  base := (-2947799354214236202203024998625608609377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3185236087576589637110346884400000000000000)
      constant := (43164880848262766761875035378468142137686324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree094.table
  base := (-5895604957072357821264082562320569849259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-14712506366876955058164977164140000000000000)
      constant := (205076600246779491577351881268449886089430343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283819991005605299521/100000000000000000000)
  centralHi := (141909995502802649761/50000000000000000000)
  directionLo := (285341824922803547551/100000000000000000000)
  directionHi := (8916932028837610861/3125000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree095.table
  base := (-5792718107784039103590570150841622022347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3220174184357936601544314334020000000000000)
      constant := (44186441239318287784487531641877563125429982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree095.table
  base := (-2896361815784935767744542781042856669663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-14873759121252402586321750008540000000000000)
      constant := (209908944857582671035731682803360601252071702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285341824922803547551/100000000000000000000)
  centralHi := (8916932028837610861/3125000000000000000)
  directionLo := (286855585279648808847/100000000000000000000)
  directionHi := (17928474079978050553/6250000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree096.table
  base := (-142164795523445036942662653261481240207/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1085037427046427855326093927880000000000000)
      constant := (15073256678310137779696743065454993538388560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree096.table
  base := (-5686596703415173594030597588047882558877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1670556875069761123830946983660000000000000)
      constant := (23866308305698900742472173296956961263845081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286855585279648808847/100000000000000000000)
  centralHi := (17928474079978050553/6250000000000000000)
  directionLo := (72090349805809597099/25000000000000000000)
  directionHi := (288361399223238388397/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree097.table
  base := (-2788609990993070318598679414764374694527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3290050377920630530412249233260000000000000)
      constant := (46264867195674807379212738779263547679618124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree097.table
  base := (-1394306074286760685304498557374627377523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-15196264630003297642635295697340000000000000)
      constant := (219740089763136994238157747971573471918148284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72090349805809597099/25000000000000000000)
  centralHi := (288361399223238388397/100000000000000000000)
  directionLo := (289859390597989541247/100000000000000000000)
  directionHi := (2264526489046793291/781250000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree098.table
  base := (-2732301358876412816117495960097297221701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-67856907646979132547881973120000000000000)
      constant := (965749646617658812328663927978832433339588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree098.table
  base := (-1092921306223015619582525020498271640363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-313418722130178472873307521260000000000000)
      constant := (4586507953807077838092993513432733328550995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289859390597989541247/100000000000000000000)
  centralHi := (2264526489046793291/781250000000000000)
  directionLo := (58269936012901838881/20000000000000000000)
  directionHi := (145674840032254597203/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree099.table
  base := (-5348740148487534987356431078379897707383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1119975523827774819760061377500000000000000)
      constant := (16130122155116143709183908240913770024676466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree099.table
  base := (-5348743518056765815981196619189110748269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1724307793194910299883204598460000000000000)
      constant := (25532574946929763554280745516579200720004457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58269936012901838881/20000000000000000000)
  centralHi := (145674840032254597203/50000000000000000000)
  directionLo := (73208096303254714249/25000000000000000000)
  directionHi := (292832385213018856997/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree100.table
  base := (-653704048560476430565751647637990522427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3394864668264671423714151582120000000000000)
      constant := (49470768505321953783416800492755446291251696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree100.table
  base := (-2614817682803702755009580965377710891659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-15680022893129640227105614230540000000000000)
      constant := (234902943978198666613958045925610576980670286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73208096303254714249/25000000000000000000)
  centralHi := (292832385213018856997/100000000000000000000)
  directionLo := (294307620671636471931/100000000000000000000)
  directionHi := (73576905167909117983/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree101.table
  base := (-1276819886656553060230659715880346661473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3429802765046018388148119031740000000000000)
      constant := (50562938772173789943969162994269712326107752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree101.table
  base := (-2553641088375600492742855372608654760519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-15841275647505087755262387074940000000000000)
      constant := (240068197967791096308228183003677499503666726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294307620671636471931/100000000000000000000)
  centralHi := (73576905167909117983/25000000000000000000)
  directionLo := (147887749104898697661/50000000000000000000)
  directionHi := (295775498209797395323/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree102.table
  base := (-4981681726875217274587861695904711812813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1154913620609121784194028827120000000000000)
      constant := (17222292411779852839728198492541338242344326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree102.table
  base := (-622710506277596791086510087080161894441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1778058711320059475935462213260000000000000)
      constant := (27254326262280211339016372610393729612137384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147887749104898697661/50000000000000000000)
  centralHi := (295775498209797395323/100000000000000000000)
  directionLo := (9288628963658705393/3125000000000000000)
  directionHi := (297236126837078572577/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree103.table
  base := (-2426419514348702864383026176089340061667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3499678958608712317016053930980000000000000)
      constant := (52782583865576085229189252964684468043739804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree103.table
  base := (-2426420540425724663908584717005470076217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-16163781156255982811575932763740000000000000)
      constant := (250565159030923950470954875805603526178329818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9288628963658705393/3125000000000000000)
  centralHi := (297236126837078572577/100000000000000000000)
  directionLo := (9334050403052287241/3125000000000000000)
  directionHi := (298689612897673191713/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree104.table
  base := (-4720751547447489802955714308002347648603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3534617055390059281450021380600000000000000)
      constant := (53910058634849084687330575433607309791310718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree104.table
  base := (-2360376679947926332813839163434923402949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-16325033910631430339732705608140000000000000)
      constant := (255896865858270016466350404027951192675796946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9334050403052287241/3125000000000000000)
  centralHi := (298689612897673191713/100000000000000000000)
  directionLo := (150068030080373762891/50000000000000000000)
  directionHi := (300136060160747525783/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree105.table
  base := (-4585419374707986072725333738342764580953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (-24282688110009566298530536260000000000000)
      constant := (374485044328117666805383863598314470838094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree105.table
  base := (-4585420975303684705150170005645605302763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (-37383869988677727591586118940000000000000)
      constant := (592480854254427769743877087983063184091711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150068030080373762891/50000000000000000000)
  centralHi := (300136060160747525783/100000000000000000000)
  directionLo := (150787784953448613841/50000000000000000000)
  directionHi := (301575569906897227683/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree106.table
  base := (-555855324823949574634424880651244972667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3604493248952753210317956279840000000000000)
      constant := (56200312483823587823025666920528271824287216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree106.table
  base := (-4446844011970903181540537850366720152339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-16647539419382325396046251296940000000000000)
      constant := (266726731522404488359441804181564829238455503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150787784953448613841/50000000000000000000)
  centralHi := (301575569906897227683/100000000000000000000)
  directionLo := (18938015063181682613/6250000000000000000)
  directionHi := (303008241010906921809/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree107.table
  base := (-4305021304010750879058690244372478284809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3639431345734100174751923729460000000000000)
      constant := (57363091512655702821335775023699491384266154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree107.table
  base := (-1076255637990507885826991947337223596841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-16808792173757772924203024141340000000000000)
      constant := (272224890138304177651148776187891412725517428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18938015063181682613/6250000000000000000)
  centralHi := (303008241010906921809/100000000000000000000)
  directionLo := (152217085010502232731/50000000000000000000)
  directionHi := (304434170021004465463/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree108.table
  base := (-2079977786459107678290680127337752143937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1224789814171815713061963726360000000000000)
      constant := (19512546192878509560859114433441800579788348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree108.table
  base := (-4159956674708839298806725475654999462761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1885560547570357828039977442860000000000000)
      constant := (30864281385423720363624224262278715078974133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152217085010502232731/50000000000000000000)
  centralHi := (304434170021004465463/100000000000000000000)
  directionLo := (152926725617394826779/50000000000000000000)
  directionHi := (305853451234789653559/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree109.table
  base := (-4011645484522199787148245520499265418557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3709307539296794103619858628700000000000000)
      constant := (59723953658475851738043949835758215966944242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree109.table
  base := (-4011646457188236002488788182804298088291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-17131297682508667980516569830140000000000000)
      constant := (283387658412091953883309564766549913629191007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152926725617394826779/50000000000000000000)
  centralHi := (305853451234789653559/100000000000000000000)
  directionLo := (307266176772006344581/100000000000000000000)
  directionHi := (153633088386003172291/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree110.table
  base := (-3860091115478971395880664408834391291761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3744245636078141068053826078320000000000000)
      constant := (60922036729639729423549927030102688960222266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree110.table
  base := (-3860091974081866023675704914392541251769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-17292550436884115508673342674540000000000000)
      constant := (289052267869335773982611006074258667923909613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307266176772006344581/100000000000000000000)
  centralHi := (153633088386003172291/50000000000000000000)
  directionLo := (308672436644316931349/100000000000000000000)
  directionHi := (6173448732886338627/2000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree111.table
  base := (-3705292540065620710322293075475955749987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1259727910953162677495931175980000000000000)
      constant := (20710629256763232374665811364518356336501274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree111.table
  base := (-3705293297919581486194255844539043108667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1939311465695507004092235057660000000000000)
      constant := (32752484527176438801188834679252760663025951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308672436644316931349/100000000000000000000)
  centralHi := (6173448732886338627/2000000000000000000)
  directionLo := (3100723188222287097/1000000000000000000)
  directionHi := (310072318822228709701/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree112.table
  base := (-1773624915167650618960347697722169615929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-77839221013078265243301244440000000000000)
      constant := (1292928709372288320575446678507333964608852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree112.table
  base := (-1773625249604350040843016337860147358831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-359490937666020623775242619660000000000000)
      constant := (6133631366215659148194556266555552042623126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3100723188222287097/1000000000000000000)
  centralHi := (310072318822228709701/100000000000000000000)
  directionLo := (155732954649656479827/50000000000000000000)
  directionHi := (62293181859862591931/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree113.table
  base := (-1692981528128491485123514195862652100831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3849059926422181961355728427180000000000000)
      constant := (64586893675926143998626366325257760564711372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree113.table
  base := (-677192729310143578677790338675893169053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-17776308700010458093143661207740000000000000)
      constant := (306378996378514041816988477672458966686714405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155732954649656479827/50000000000000000000)
  centralHi := (62293181859862591931/20000000000000000000)
  directionLo := (156426646076924699429/50000000000000000000)
  directionHi := (312853292153849398859/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree114.table
  base := (-322143228584151223058769183635264246609/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1294666007734509641929898625600000000000000)
      constant := (21944016166782185725413223265257441038323180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree114.table
  base := (-1610716403373470299803372381463363203481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-1993062383820656180144492672460000000000000)
      constant := (34696170995338894718296592965449771218176586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156426646076924699429/50000000000000000000)
  centralHi := (312853292153849398859/100000000000000000000)
  directionLo := (62846909921604210713/20000000000000000000)
  directionHi := (157117274804010526783/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree115.table
  base := (-47713399769618020811664604259874594729/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3918936119984875890223663326420000000000000)
      constant := (67088971213050367933013666069071199625579136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree115.table
  base := (-1526829022447157841873777679503195454003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-18098814208761353149457206896540000000000000)
      constant := (318207564597052068684026860294034544828708062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62846909921604210713/20000000000000000000)
  centralHi := (157117274804010526783/50000000000000000000)
  directionLo := (63121952416955495533/20000000000000000000)
  directionHi := (157804881042388738833/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree116.table
  base := (-57652780378495942495253460077857261597/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-3953874216766222854657630776040000000000000)
      constant := (68357661795096423158919255010775498254524100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree116.table
  base := (-576527884894518053302083007717237990833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-18260066963136800677613979740940000000000000)
      constant := (324205073211536385034376229737550470690639705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63121952416955495533/20000000000000000000)
  centralHi := (157804881042388738833/50000000000000000000)
  directionLo := (316979008262477598629/100000000000000000000)
  directionHi := (31697900826247759863/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree117.table
  base := (-2708376649627654496158931089341881885671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1329604104515856606363866075220000000000000)
      constant := (23212706742675956684380775429559495575204242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree117.table
  base := (-33854712592797262736516554176172624257/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-2046813301945805356196750287260000000000000)
      constant := (36695340524394857051105560701688209938737680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316979008262477598629/100000000000000000000)
  centralHi := (31697900826247759863/10000000000000000000)
  directionLo := (159171182563708623387/50000000000000000000)
  directionHi := (12733694605096689871/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree118.table
  base := (-316358817322563293863807077145656494991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4023750410328916783525565675280000000000000)
      constant := (70930346493847092629678986482453415923781168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree118.table
  base := (-63271771355620545020457890643597416379/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-18582572471887695733927525429740000000000000)
      constant := (336366539041093070464182593187940824725223320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159171182563708623387/50000000000000000000)
  centralHi := (12733694605096689871/4000000000000000000)
  directionLo := (63939981604868119953/20000000000000000000)
  directionHi := (159849954012170299883/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree119.table
  base := (-470024149103090606202076286984085042469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60000000000000000000000000000000000000000
      center := (87)
      previous := (39)
      next := (0)
      square := (1151805388396053772548377460000000000000)
      linear := (-82830377696127831591010880100000000000000)
      constant := (1474170215816180681387413363855477448725930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree119.table
  base := (-2350121023954149005030814453449506428739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (387)
      previous := (180)
      next := (0)
      square := (5183124247782241976467698570000000000000)
      linear := (-382527045433941699226210168860000000000000)
      constant := (6990418287714156830599194701356863326424047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63939981604868119953/20000000000000000000)
  centralHi := (159849954012170299883/50000000000000000000)
  directionLo := (321051710705029319343/100000000000000000000)
  directionHi := (20065731919064332459/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree120.table
  base := (-433225465750278660083019462477039233809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1364542201297203570797833524840000000000000)
      constant := (24516700818106465363817317382586250775433590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree120.table
  base := (-433225514870578431528401997048583809753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-2100564220070954532249007902060000000000000)
      constant := (38749992868207115755830647620169290899831545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321051710705029319343/100000000000000000000)
  centralHi := (20065731919064332459/6250000000000000000)
  directionLo := (322397845375058045351/100000000000000000000)
  directionHi := (40299730671882255669/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree121.table
  base := (-1978890345259163993263915711554218004467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4128564700672957676827468024140000000000000)
      constant := (74877632115077294710848120869148059906686702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree121.table
  base := (-989445280940628228651091401407275504631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-19066330735014038318397843962940000000000000)
      constant := (355024858114007290295714136623476349014746374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322397845375058045351/100000000000000000000)
  centralHi := (40299730671882255669/12500000000000000000)
  directionLo := (80934595684700029781/25000000000000000000)
  directionHi := (2589907061910400953/800000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree122.table
  base := (-894204925360692248112161880602049765717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4163502797454304641261435473760000000000000)
      constant := (76216929540895859146491519777225994737758404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree122.table
  base := (-1788410041770613171151515416271059156297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-19227583489389485846554616807340000000000000)
      constant := (361355262925352325992649003031473388736219069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80934595684700029781/25000000000000000000)
  centralHi := (2589907061910400953/800000000000000000)
  directionLo := (81268348010690727939/25000000000000000000)
  directionHi := (325073392042762911757/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree123.table
  base := (-159468589958757391777655446377056043909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1399480298078550535231800974460000000000000)
      constant := (25855998238588976926829653456425485076969180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree123.table
  base := (-398671517017937966599218844279996718219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-2154315138196103708301265516860000000000000)
      constant := (40860127797376661588429526892763361929687228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81268348010690727939/25000000000000000000)
  centralHi := (325073392042762911757/100000000000000000000)
  directionLo := (326402941117327912153/100000000000000000000)
  directionHi := (163201470558663956077/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree124.table
  base := (-349429636281260445613001895649311297933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4233378991016998570129370373000000000000000)
      constant := (78930827624029920612628211114876409913630792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree124.table
  base := (-1397718693699694231243288011225326469883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-19550088998140380902868162496140000000000000)
      constant := (374182519797113601511869105127548893080344791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326402941117327912153/100000000000000000000)
  centralHi := (163201470558663956077/50000000000000000000)
  directionLo := (40965887052120845741/12500000000000000000)
  directionHi := (327727096416966765929/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree125.table
  base := (-1197507839465994231232545899791685928237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4268317087798345534563337822620000000000000)
      constant := (80305428250357960037460604356086244337098322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree125.table
  base := (-598753985237710877160022224757764172337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-19711341752515828431024935340540000000000000)
      constant := (380679371718964109131202540143290955999996298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40965887052120845741/12500000000000000000)
  centralHi := (327727096416966765929/100000000000000000000)
  directionLo := (20565370191187545733/6250000000000000000)
  directionHi := (329045923059000731729/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree126.table
  base := (-497026916825623003299621756459298110703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (383935129465351257516125820000000000000)
      linear := (-29273844793059132646240171920000000000000)
      constant := (555726507345204418508140845634162807557188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree126.table
  base := (-994053949164827938414161396905763153013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (43)
      previous := (20)
      next := (0)
      square := (575902694198026886274188730000000000000)
      linear := (-45062572577984752741908635340000000000000)
      constant := (878076430555052607822400961409282710540961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20565370191187545733/6250000000000000000)
  centralHi := (329045923059000731729/100000000000000000000)
  directionLo := (330359484860967520091/100000000000000000000)
  directionHi := (82589871215241880023/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree127.table
  base := (-31494263106835322900547079408059045099/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4338193281361039463431272721860000000000000)
      constant := (83089932597494103788931807461695766018522350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree127.table
  base := (-787356679515169280577600630515451356979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-20033847261266723487338481029340000000000000)
      constant := (393839522198740253921698211211028057854716783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330359484860967520091/100000000000000000000)
  centralHi := (82589871215241880023/25000000000000000000)
  directionLo := (331667844376656186469/100000000000000000000)
  directionHi := (33166784437665618647/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree128.table
  base := (-288708060251090397383076088346839140659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2940000000000000000000000000000000000000000
      center := (4263)
      previous := (1911)
      next := (0)
      square := (56438464031406634854870495540000000000000)
      linear := (-4373131378142386427865240171480000000000000)
      constant := (84499836289205803884623563893652058585292508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree128.table
  base := (-577416210289257308540651359505370229611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (18963)
      previous := (8820)
      next := (0)
      square := (253973088141329856846917229930000000000000)
      linear := (-20195100015642171015495253873740000000000000)
      constant := (400502820626337071096073529208174395186224647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell008.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331667844376656186469/100000000000000000000)
  centralHi := (33166784437665618647/10000000000000000000)
  directionLo := (83242765732716912687/25000000000000000000)
  directionHi := (332971062930867650749/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree129.table
  base := (-364232510145047509726221757660772461287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1421)
      previous := (637)
      next := (0)
      square := (18812821343802211618290165180000000000000)
      linear := (-1469356491641244464099735873700000000000000)
      constant := (28640502546922725585626441706344244298793874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 20
  qDenominator := 63
  table := BinomialMassData.Q20_63.Degree129.table
  base := (-182116294648802978456975213827640704829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (2107)
      previous := (980)
      next := (0)
      square := (28219232015703317427435247770000000000000)
      linear := (-2261816974446402060405780746460000000000000)
      constant := (45246844566035037959701656158734673632780274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q20_63.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell008.Kernel129
