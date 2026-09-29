import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell062.Parameters
import ForestUnimodality.BinomialMassData.Q49_99.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_99.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_99.Batch100_149
import ForestUnimodality.BinomialMassData.Q49_99.Batch150_199
import ForestUnimodality.BinomialMassData.Q131_264.Batch000_049
import ForestUnimodality.BinomialMassData.Q131_264.Batch050_099
import ForestUnimodality.BinomialMassData.Q131_264.Batch100_149
import ForestUnimodality.BinomialMassData.Q131_264.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree000.table
  base := (729288617661044315421037259/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (8124690470987019083951019600000000000)
      constant := (729288617661044315421037259000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree000.table
  base := (729288617661044315421037259/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (8124690470987019083951019600000000000)
      constant := (729288617661044315421037259000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree001.table
  base := (51774175692908056876077655805803290062079/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-209151433581602597819781506038800000000000)
      constant := (123066603979809514113340512995637417187499704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree001.table
  base := (413392519449116812408973460513092987163299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-23299015428185857167755687450700000000000)
      constant := (13647667247851510624658010702231899826388867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24998724587403195307/50000000000000000000)
  directionHi := (9999489834961278123/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree002.table
  base := (247061217025065441510494157480536030283899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-420715900233088340307496464898800000000000)
      constant := (73584220249282790215347457575676800994318003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree002.table
  base := (30776898253910902028548613996986053420091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-46866145641914285965281758548200000000000)
      constant := (8148223646768026221059379512295543102904024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24998724587403195307/50000000000000000000)
  centralHi := (9999489834961278123/20000000000000000000)
  directionLo := (7070707070707070707/10000000000000000000)
  directionHi := (70707070707070707071/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree003.table
  base := (19517695924503271632120586114760516790367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-70253374098286009199467935973200000000000)
      constant := (5204630477194991414530064735266376432656888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree003.table
  base := (38863904293418244379935188668097003330251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-23477758618547571587602609881900000000000)
      constant := (1727420190615295023077807213187661896531044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7070707070707070707/10000000000000000000)
  centralHi := (70707070707070707071/100000000000000000000)
  directionLo := (86598122219607306501/100000000000000000000)
  directionHi := (43299061109803653251/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree004.table
  base := (104891600019582064117443029065961533030969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-843844833536059825282926382618800000000000)
      constant := (31985737695166229757024714047945775310197793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree004.table
  base := (6523817675766432114660721095536551003759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-94000406069371143560333900743200000000000)
      constant := (3537597930972718148381041198591998929984752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86598122219607306501/100000000000000000000)
  centralHi := (43299061109803653251/50000000000000000000)
  directionLo := (24998724587403195307/25000000000000000000)
  directionHi := (99994898349612781229/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree005.table
  base := (74630236155766737760160035089698362473979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-1055409300187545567770641341478800000000000)
      constant := (23468130064746697345374416445484413654771763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree005.table
  base := (74258757572193843070707201758309656819907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-117567536283099572357859971840700000000000)
      constant := (2596052486778040449130494249438999925056931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24998724587403195307/25000000000000000000)
  centralHi := (99994898349612781229/100000000000000000000)
  directionLo := (111797695056457855171/100000000000000000000)
  directionHi := (27949423764114463793/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree006.table
  base := (55723092699278744591064237515194604307383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-12797714816555871820791477781200000000000)
      constant := (186135753749715101270569731072783812922149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree006.table
  base := (27725081581317814551500807412420620078609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-47044888832276000385128680979400000000000)
      constant := (679851485221485826450652806130728641729398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111797695056457855171/100000000000000000000)
  centralHi := (27949423764114463793/25000000000000000000)
  directionLo := (30617059729752881451/25000000000000000000)
  directionHi := (24493647783802305161/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree007.table
  base := (43163844295838324595769653781530889857453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-1478538233490517052746071259198800000000000)
      constant := (15376787734370434073988038019516274287663541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree007.table
  base := (21478932316506884747977998952520237833737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-164701796710556429952912114035700000000000)
      constant := (1703188484263010658673974004287966947026642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30617059729752881451/25000000000000000000)
  centralHi := (24493647783802305161/20000000000000000000)
  directionLo := (16535102088016155113/12500000000000000000)
  directionHi := (26456163340825848181/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree008.table
  base := (134015351577118989546675753878807337899/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-1690102700142002795233786218058800000000000)
      constant := (13530739804506818604232114979383879515136768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree008.table
  base := (3414721434454827892693837083901711644361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-17115356993116805340948925921200000000000)
      constant := (136364654590360042859062332895451349330830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16535102088016155113/12500000000000000000)
  centralHi := (26456163340825848181/20000000000000000000)
  directionLo := (141414141414141414141/100000000000000000000)
  directionHi := (70707070707070707071/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree009.table
  base := (2772644650443959904321626942512315110203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-70432117288647723619314858404400000000000)
      constant := (461663390593375428296296166505954662122330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree009.table
  base := (27596986305669799979469902400091699617907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-70612019046004429182654752076900000000000)
      constant := (461040715545172707645097320199252445796977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141414141414141414141/100000000000000000000)
  centralHi := (70707070707070707071/50000000000000000000)
  directionLo := (74996173762209585921/50000000000000000000)
  directionHi := (149992347524419171843/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree010.table
  base := (11311420911852051319418512780571542268729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-2113231633444974280209216135778800000000000)
      constant := (11942727022568374324215548685847496107625026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree010.table
  base := (22515816631949214884164329356450437070767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-235403187351741716345490327328200000000000)
      constant := (1326406314501522726741046213881489423335311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74996173762209585921/50000000000000000000)
  centralHi := (149992347524419171843/100000000000000000000)
  directionLo := (79052908295447110479/50000000000000000000)
  directionHi := (158105816590894220959/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree011.table
  base := (18534541729067464291384354477331647833353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-211345100008769092972448281330800000000000)
      constant := (1075163789736853187500816381236754491500531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree011.table
  base := (18444396051955549948018320039686753090019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-23542756142315467740274218038700000000000)
      constant := (119518772557704740999803497876704009270057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79052908295447110479/50000000000000000000)
  centralHi := (158105816590894220959/100000000000000000000)
  directionLo := (82911389693848502227/50000000000000000000)
  directionHi := (33164555877539400891/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree012.table
  base := (7589665260274419287995815404194868478751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-281817840749771751687182894833200000000000)
      constant := (1337035275193095298632767031715261319597566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree012.table
  base := (755124018069612183279172125199710353511/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-94179149259732857980180823174400000000000)
      constant := (446258212931139955341956831557636277772420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82911389693848502227/50000000000000000000)
  centralHi := (33164555877539400891/20000000000000000000)
  directionLo := (173196244439214613003/100000000000000000000)
  directionHi := (43299061109803653251/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree013.table
  base := (48341633567940852766381460032384492691/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-2747925033399431507672361012358800000000000)
      constant := (12508294640053448145987153327896657748282112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree013.table
  base := (6154742164248393339847990699968510572939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-306104577992927002738068540620700000000000)
      constant := (1392651423829363063038739661437602947813974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173196244439214613003/100000000000000000000)
  centralHi := (43299061109803653251/25000000000000000000)
  directionLo := (180268366642169160657/100000000000000000000)
  directionHi := (90134183321084580329/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree014.table
  base := (2499863772918661063215403208481746734049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-2959489500050917250160075971218800000000000)
      constant := (13215062689242467304552473595619515120050212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree014.table
  base := (1242827987642856418724101461020283191261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-329671708206655431535594611718200000000000)
      constant := (1472284979522412929897862850639179762492904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180268366642169160657/100000000000000000000)
  centralHi := (90134183321084580329/50000000000000000000)
  directionLo := (187073325024769031651/100000000000000000000)
  directionHi := (46768331256192257913/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree015.table
  base := (7963358866088306078035095592083656337251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-352339329633600332516421214453200000000000)
      constant := (1569721867395673970533180177986760659129283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree015.table
  base := (7914347397608075521687755215297666235627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-117746279473461286777706894271900000000000)
      constant := (524928700125243838505032061072118078591897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187073325024769031651/100000000000000000000)
  centralHi := (46768331256192257913/25000000000000000000)
  directionLo := (193639288006876908797/100000000000000000000)
  directionHi := (96819644003438454399/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree016.table
  base := (6202036228120129959795033630654436140267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-3382618433353888735135505888938800000000000)
      constant := (15226252405320670431021634028285167533659299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree016.table
  base := (1539944570738979847490822061128634325293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-376805968634112289130646753913200000000000)
      constant := (1698013860736413006311661375853779730938676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193639288006876908797/100000000000000000000)
  centralHi := (96819644003438454399/50000000000000000000)
  directionLo := (24998724587403195307/12500000000000000000)
  directionHi := (199989796699225562457/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree017.table
  base := (2332917098794424398626323168209482116759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-326743900000488588874838258890800000000000)
      constant := (1499689322764313187659776639336912034304986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree017.table
  base := (289339712009931225229851696336026911659/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-400373098847840717928172825010700000000000)
      constant := (1840335382158550451706479568615053459355952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24998724587403195307/12500000000000000000)
  centralHi := (199989796699225562457/100000000000000000000)
  directionLo := (103072381979588644687/50000000000000000000)
  directionHi := (329831622334683663/160000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree018.table
  base := (829026918910882168262074339042383086059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-140953606172476304448553178024400000000000)
      constant := (663963320276394898557427282157064855786596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree018.table
  base := (328479852986556581152586305804587820891/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-141313409687189715575232965369400000000000)
      constant := (666826499398515330035496256507179660298010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103072381979588644687/50000000000000000000)
  centralHi := (329831622334683663/160000000000000000)
  directionLo := (53030303030303030303/25000000000000000000)
  directionHi := (212121212121212121213/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree019.table
  base := (2122347702706694579910000609236751514579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-4017311833308345962598650765518800000000000)
      constant := (19508472535491811944240834918930515199829963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree019.table
  base := (2095457056324826723899352219475679013089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-40682487206845234138474997018700000000000)
      constant := (197949332521419418995873066726970787039267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53030303030303030303/25000000000000000000)
  centralHi := (212121212121212121213/100000000000000000000)
  directionLo := (108966914193896048363/50000000000000000000)
  directionHi := (217933828387792096727/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree020.table
  base := (1060236988650655835217938631748828433007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-4228876299959831705086365724378800000000000)
      constant := (21233748979326969981090352148005402044603079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree020.table
  base := (207435193244297011318131611611463130339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-471074489489026004320751038303200000000000)
      constant := (2370425105603351797871979055309391416505935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108966914193896048363/50000000000000000000)
  centralHi := (217933828387792096727/100000000000000000000)
  directionLo := (223595390112915710343/100000000000000000000)
  directionHi := (27949423764114463793/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree021.table
  base := (110269328021520020828955085876979676661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-493382307401257494174897853693200000000000)
      constant := (2566338403994258924823396763681140329329813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree021.table
  base := (90520631729060787612713584562803931287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-164880539900918144372759036466900000000000)
      constant := (859595166360162238711013840938384593244157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223595390112915710343/100000000000000000000)
  centralHi := (27949423764114463793/12500000000000000000)
  directionLo := (229117095398257684933/100000000000000000000)
  directionHi := (114558547699128842467/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree022.table
  base := (-743269275448804138698605416425033309797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-422909566660254835460163240190800000000000)
      constant := (2281245040769479078399574494914124100635481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree022.table
  base := (-380079713227940033570055872619261937613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-47109886356043896537800289136200000000000)
      constant := (254727942940909549296573211686759428374322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229117095398257684933/100000000000000000000)
  centralHi := (114558547699128842467/50000000000000000000)
  directionLo := (117254411780241408807/50000000000000000000)
  directionHi := (46901764712096563523/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree023.table
  base := (-75653742454539015901037633168522280931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-4863569699914288932549510600958800000000000)
      constant := (27219927696757640886671762953681377651269860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree023.table
  base := (-763751722245536135502235793320814812647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-541775880130211290713329251595700000000000)
      constant := (3039673630618701529069660901902257472365298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117254411780241408807/50000000000000000000)
  centralHi := (46901764712096563523/20000000000000000000)
  directionLo := (59944835709440501229/25000000000000000000)
  directionHi := (239779342837762004917/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree024.table
  base := (-2209426210581724886023058332917383911177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-563903796285086075004136173313200000000000)
      constant := (3274743285775364492742320734850526330931159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree024.table
  base := (-138858714961483188084827056095552128697/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-188447670114646573170285107564400000000000)
      constant := (1097148916441779358479223877749582825349328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59944835709440501229/25000000000000000000)
  centralHi := (239779342837762004917/100000000000000000000)
  directionLo := (244936477838023051609/100000000000000000000)
  directionHi := (24493647783802305161/10000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree025.table
  base := (-177541115979087191004824775212146095277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-5286698633217260417524940518678800000000000)
      constant := (31849505728890292614051303252411881755243696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree025.table
  base := (-570231321594367093309385473771401272861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-588910140557668148308381393790700000000000)
      constant := (3557053184974261368282835976792250039977935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244936477838023051609/100000000000000000000)
  centralHi := (24493647783802305161/10000000000000000000)
  directionLo := (249987245874031953071/100000000000000000000)
  directionHi := (15624202867126997067/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree026.table
  base := (-3413535794766419217828257115713003211509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-5498263099868746160012655477538800000000000)
      constant := (34348366662397562793058421068402038046181827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree026.table
  base := (-684496151645903240085472946692369759097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-612477270771396577105907464888200000000000)
      constant := (3836270985902325099195978211349183989748995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249987245874031953071/100000000000000000000)
  centralHi := (15624202867126997067/6250000000000000000)
  directionLo := (254937968972201263149/100000000000000000000)
  directionHi := (5098759379444025263/2000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree027.table
  base := (-3933558173846257449107080673591144373699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-211475095056304885277791497644400000000000)
      constant := (1369171830487019901058758537819297411889311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree027.table
  base := (-3941174541669533070345862956533939630323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-212014800328375001967811178661900000000000)
      constant := (1376306628203202730939545614689420414066447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254937968972201263149/100000000000000000000)
  centralHi := (5098759379444025263/2000000000000000000)
  directionLo := (51958873331764383901/20000000000000000000)
  directionHi := (129897183329410959753/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree028.table
  base := (-2202598379145793096385592215950169077667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-538308366651974331362553217750800000000000)
      constant := (3609635990620579392464254450561090869805982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree028.table
  base := (-2205839272721346822340362708021805984269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-659611531198853434700959607083200000000000)
      constant := (4434853341720133999394327863476460805038246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51958873331764383901/20000000000000000000)
  centralHi := (129897183329410959753/50000000000000000000)
  directionLo := (16535102088016155113/6250000000000000000)
  directionHi := (264561633408258481809/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree029.table
  base := (-4832091471050422088828324685576983086441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-6132956499823203387475800354118800000000000)
      constant := (42562355026312509816537072753958836023327023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree029.table
  base := (-4837605435430106419454947505872099665927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-683178661412581863498485678180700000000000)
      constant := (4753952139259825938554292421575701961024409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16535102088016155113/6250000000000000000)
  centralHi := (264561633408258481809/100000000000000000000)
  directionLo := (3365556296783292803/1250000000000000000)
  directionHi := (269244503742663424241/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree030.table
  base := (-5217207423964631269016447164768956434749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-704946774052743236662612812553200000000000)
      constant := (5059537352598990287305681336958624437653283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree030.table
  base := (-522189659660730551390637596154004351993/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-21416539140191220978667022705400000000000)
      constant := (154124824591651254071626714427084956480070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3365556296783292803/1250000000000000000)
  centralHi := (269244503742663424241/100000000000000000000)
  directionLo := (54769461461519026659/20000000000000000000)
  directionHi := (17115456706724695831/6250000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree031.table
  base := (-111259237122705176365594537698062142737/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-6556085433126174872451230271838800000000000)
      constant := (48625721418048571234520556812596577180355550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree031.table
  base := (-5566948693016917585834780342348936474587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-730312921840038721093537820375700000000000)
      constant := (5431275468600723657115102931573816346338629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54769461461519026659/20000000000000000000)
  centralHi := (17115456706724695831/6250000000000000000)
  directionLo := (34796751968486538597/12500000000000000000)
  directionHi := (278374015747892308777/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree032.table
  base := (-2935663429457112568111180561119174210027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-6767649899777660614938945230698800000000000)
      constant := (51831425049153965404162900502816810519243962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree032.table
  base := (-22948109508195547980801031831342614051/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-753880052053767149891063891473200000000000)
      constant := (5789356418277031874429674672498417596497152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34796751968486538597/12500000000000000000)
  centralHi := (278374015747892308777/100000000000000000000)
  directionLo := (141414141414141414141/50000000000000000000)
  directionHi := (282828282828282828283/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree033.table
  base := (-23999658516465295963052262323706344739/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-70497114812415619771986466561200000000000)
      constant := (557095644977543032204041872804993527240448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree033.table
  base := (-3073396722553408717496888281318318408529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-23559005523257441778442120077900000000000)
      constant := (186676043373332280907251232602194613182942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141414141414141414141/50000000000000000000)
  centralHi := (282828282828282828283/100000000000000000000)
  directionLo := (287213478951776376379/100000000000000000000)
  directionHi := (14360673947588818819/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree034.table
  base := (-1276406933872008320202605827316487064177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-7190778833080632099914375148418800000000000)
      constant := (58588462081068288651774745825554216709697155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree034.table
  base := (-3192241702900509728769502124324964485481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-801014312481224007486116033668200000000000)
      constant := (6544091525897515439916674081755377343958254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287213478951776376379/100000000000000000000)
  centralHi := (14360673947588818819/5000000000000000000)
  directionLo := (58306544200653785553/20000000000000000000)
  directionHi := (145766360501634463883/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree035.table
  base := (-823346123199225010226528444071712741987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-7402343299732117842402090107278800000000000)
      constant := (62139085203832845954560751560293610525038888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree035.table
  base := (-1647212620432638653999006776551243240497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-824581442694952436283642104765700000000000)
      constant := (6940667571346536071607740653469017142254396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58306544200653785553/20000000000000000000)
  centralHi := (145766360501634463883/50000000000000000000)
  directionLo := (295788898269622668477/100000000000000000000)
  directionHi := (147894449134811334239/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree036.table
  base := (-1689749001204723937365256155648386434963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-281996583940133466107029817264400000000000)
      constant := (2437188026656569935111967173949870996861628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree036.table
  base := (-6760765482567421273036596336521263241643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-282716190969560288360389391954400000000000)
      constant := (2450002943649283739681440867124366104341927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295788898269622668477/100000000000000000000)
  centralHi := (147894449134811334239/50000000000000000000)
  directionLo := (59996939009767668737/20000000000000000000)
  directionHi := (149992347524419171843/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree037.table
  base := (-3449718443889676278125245814646092744713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-7825472233035089327377520024998800000000000)
      constant := (69583222444010940418331384063665820909640478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree037.table
  base := (-345047065482287569897468846947453344193/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-871715703122409293878694246960700000000000)
      constant := (7772091778957434527239893980489062042832620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59996939009767668737/20000000000000000000)
  centralHi := (149992347524419171843/50000000000000000000)
  directionLo := (9503831576593811143/3125000000000000000)
  directionHi := (304122610451001956577/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree038.table
  base := (-7008682794437461998216843065851072842243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-8037036699686575069865234983858800000000000)
      constant := (73476346802174701891162806956876631365853829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree038.table
  base := (-7009962075786503001777436857069899394463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-895282833336137722676220318058200000000000)
      constant := (8206897139652194381830033548678718319982721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9503831576593811143/3125000000000000000)
  centralHi := (304122610451001956577/100000000000000000000)
  directionLo := (77051243951476552691/25000000000000000000)
  directionHi := (61640995161181242153/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree039.table
  base := (-1771804681196098319491891918687258929343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-83319203700384452650029797401200000000000)
      constant := (782659654032538337508514729492552892847884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree039.table
  base := (-7088306775621443233878451243199390291161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-306283321183288717157915463051900000000000)
      constant := (2884803035403094155628646008638550456797229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77051243951476552691/25000000000000000000)
  centralHi := (61640995161181242153/20000000000000000000)
  directionLo := (312233970021691555471/100000000000000000000)
  directionHi := (19514623126355722217/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree040.table
  base := (-7135442921019385713340368216886393777097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-8460165632989546554840664901578800000000000)
      constant := (81603981007217546907474040132336741048202191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree040.table
  base := (-285454741566291950525192445353401218571/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-942417093763594580271272460253200000000000)
      constant := (9114614705338476802334653507995443994678925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312233970021691555471/100000000000000000000)
  centralHi := (19514623126355722217/6250000000000000000)
  directionLo := (79052908295447110479/25000000000000000000)
  directionHi := (316211633181788441917/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree041.table
  base := (-7153682668224262154684518494073614891919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-8671730099641032297328379860438800000000000)
      constant := (85838275372494154987002318375460936377100057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree041.table
  base := (-7154470303480069803349280256164063448841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-87816747634302091733527139213700000000000)
      constant := (871591207283267216465472162901901559653477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79052908295447110479/25000000000000000000)
  centralHi := (316211633181788441917/100000000000000000000)
  directionLo := (320139878621019779727/100000000000000000000)
  directionHi := (20008742413813736233/6250000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree042.table
  base := (-7142207171034007950857462025024221600721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-987032729588057559979566091033200000000000)
      constant := (10020678765697169889257459136008600687176207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree042.table
  base := (-178571939448301627494425612135705438493/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-329850451397017145955441534149400000000000)
      constant := (3357688689577791338216544467936364607063080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320139878621019779727/100000000000000000000)
  centralHi := (20008742413813736233/6250000000000000000)
  directionLo := (81005125920936565773/25000000000000000000)
  directionHi := (324020503683746263093/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree043.table
  base := (-3550619027455254003933488897836639300867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-9094859032944003782303809778158800000000000)
      constant := (94647415740796489139334171319363436255285002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree043.table
  base := (-7101808849317729230498527951242990065239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1013118484404779866663850673545700000000000)
      constant := (10571295861126234031846151367382662577847113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81005125920936565773/25000000000000000000)
  centralHi := (324020503683746263093/100000000000000000000)
  directionLo := (327855199335706698321/100000000000000000000)
  directionHi := (163927599667853349161/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree044.table
  base := (-1406191587298389320609317894825479635559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-846038499963226320435593157910800000000000)
      constant := (9020194698538044969516852648353760249199535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree044.table
  base := (-3515722034855646707981068045416662548619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-94244146783500754132852431331200000000000)
      constant := (1007471519897824527494086571201200024708286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327855199335706698321/100000000000000000000)
  centralHi := (163927599667853349161/50000000000000000000)
  directionLo := (82911389693848502227/25000000000000000000)
  directionHi := (331645558775394008909/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree045.table
  base := (-6931517423316640134770425382739251887473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-352518072823962046936268136884400000000000)
      constant := (3848527481118580207742727390737868229237797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree045.table
  base := (-6931931585434097618471241029269779989913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-353417581610745574752967605246900000000000)
      constant := (3868577915518092369220008070391126170110957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82911389693848502227/25000000000000000000)
  centralHi := (331645558775394008909/100000000000000000000)
  directionLo := (67078617033874713103/20000000000000000000)
  directionHi := (83848271292343391379/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree046.table
  base := (-6803040835148084404365901079243581505361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-9729552432898461009766954654738800000000000)
      constant := (108711679736676243719444710152809456292907783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree046.table
  base := (-6803393797870900090464652730862865901557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1083819875045965153056428886838200000000000)
      constant := (12141932904915158925190886422440950425248619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67078617033874713103/20000000000000000000)
  centralHi := (83848271292343391379/25000000000000000000)
  directionLo := (169549599309035539349/50000000000000000000)
  directionHi := (339099198618071078699/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree047.table
  base := (-6645630884051193586406849284826327565751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-9941116899549946752254669613598800000000000)
      constant := (113626424417858949486010162622360180712971953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree047.table
  base := (-1329186358377585269051446527114660648339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1107387005259693581853954957935700000000000)
      constant := (12690780858158129813088148489497212243024065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169549599309035539349/50000000000000000000)
  centralHi := (339099198618071078699/100000000000000000000)
  directionLo := (42845655305447352397/12500000000000000000)
  directionHi := (342765242443578819177/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree048.table
  base := (-807421563223206671105728241922591835689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1128075707355714721638042730273200000000000)
      constant := (13183827867536572917714231982846035755378104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree048.table
  base := (-3229814561596593682870586510322843835011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-376984711824474003550493676344400000000000)
      constant := (4417424949648275136305456022397697435629758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42845655305447352397/12500000000000000000)
  centralHi := (342765242443578819177/100000000000000000000)
  directionLo := (346392488878429226007/100000000000000000000)
  directionHi := (43299061109803653251/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree049.table
  base := (-6244335998974140756192617001918498672157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-10364245832852918237230099531318800000000000)
      constant := (123795738027895928969359079389181405894369371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree049.table
  base := (-6244554920021780947018614142695954712809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1154521265687150439449007100130700000000000)
      constant := (13826412596043487485437174527060264744477303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346392488878429226007/100000000000000000000)
  centralHi := (43299061109803653251/12500000000000000000)
  directionLo := (349982144223644734299/100000000000000000000)
  directionHi := (3499821442236447343/1000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree050.table
  base := (-6000579599244624077682990741511911265641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-961437299954945816337983135470800000000000)
      constant := (11731842616552523729274555825519178395827693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree050.table
  base := (-3000383212703828991738540002114544642767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1178088395900878868246533171228200000000000)
      constant := (14413192210433995663135779577016065053577378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349982144223644734299/100000000000000000000)
  centralHi := (3499821442236447343/1000000000000000000)
  directionLo := (353535353535353535353/100000000000000000000)
  directionHi := (176767676767676767677/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree051.table
  base := (-1145630318365043454308609706678549034827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1198597196239543302467281049893200000000000)
      constant := (14935336525517989175306448867841239409253545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree051.table
  base := (-5728311082706325070907749658926038900391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-400551842038202432348019747441900000000000)
      constant := (5004204042161872741450358102763007322095699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353535353535353535353/100000000000000000000)
  centralHi := (176767676767676767677/50000000000000000000)
  directionLo := (22315825305724288407/6250000000000000000)
  directionHi := (357053204891588614513/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree052.table
  base := (-169596626463390943807076569341358975053/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-10998939232807375464693244407898800000000000)
      constant := (139899005969824914446948919605877324301096288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree052.table
  base := (-2713614123950859112937059748242085611039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-111383877848030520531053210311200000000000)
      constant := (1420424640495535025503314849092647486333766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22315825305724288407/6250000000000000000)
  centralHi := (357053204891588614513/100000000000000000000)
  directionLo := (72107346656867664263/20000000000000000000)
  directionHi := (90134183321084580329/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree053.table
  base := (-159294820182666679966267626005495942503/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-11210503699458861207180959366758800000000000)
      constant := (145493190617934319855147705101110166562451488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree053.table
  base := (-1019510119342206344396750699847523887299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1248789786542064154639111384520700000000000)
      constant := (16249367889031129420662897060789339808595665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72107346656867664263/20000000000000000000)
  centralHi := (90134183321084580329/25000000000000000000)
  directionLo := (90996731044077022993/25000000000000000000)
  directionHi := (363986924176308091973/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree054.table
  base := (-473920585578537894185028036015978549881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-423039561707790627765506456504400000000000)
      constant := (5600021276182145947246074216715842359513090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree054.table
  base := (-4739305281904330603543110157377795289367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-424118972251930861145545818539400000000000)
      constant := (5628900587061646166089420780141119251816963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90996731044077022993/25000000000000000000)
  centralHi := (363986924176308091973/100000000000000000000)
  directionLo := (183702358378517288707/50000000000000000000)
  directionHi := (73480943351406915483/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree055.table
  base := (-4352429895596382489470203822048439345391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-1057602966614712062923308116770800000000000)
      constant := (14274650059104390799727090753148692137674443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree055.table
  base := (-4352514886024739404445384670827362203477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-117811276997229182930378502428700000000000)
      constant := (1594242901517126309430371248847611663389569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183702358378517288707/50000000000000000000)
  centralHi := (73480943351406915483/20000000000000000000)
  directionLo := (370791006928841456007/100000000000000000000)
  directionHi := (46348875866105182001/12500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree056.table
  base := (-787425106622810828068009085539258637319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-11845197099413318434644104243338800000000000)
      constant := (162954913504778188726857454231107000923581285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree056.table
  base := (-3937198206380285539164883782518690258861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1319491177183249441031689597813200000000000)
      constant := (18199277735230317232382709128973683221457587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370791006928841456007/100000000000000000000)
  centralHi := (46348875866105182001/12500000000000000000)
  directionLo := (374146650049538063303/100000000000000000000)
  directionHi := (46768331256192257913/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree057.table
  base := (-43666359280964475311960107726083791393/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1339640174007200464125757689133200000000000)
      constant := (18777984252943155268718306852085538790722480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree057.table
  base := (-1746685451208374543447504088810609242201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-447686102465659289943071889636900000000000)
      constant := (6291506233349670413866918764254210346671578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374146650049538063303/100000000000000000000)
  centralHi := (46768331256192257913/12500000000000000000)
  directionLo := (377472463455652416543/100000000000000000000)
  directionHi := (11796014482989138017/3125000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree058.table
  base := (-377624105873925748387962530832895102499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-12268326032716289919619534161058800000000000)
      constant := (175161981008257128454216308162151441236462376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree058.table
  base := (-604209206015675879944211411676118183307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1366625437610706298626741740008200000000000)
      constant := (19562394380298311202769410355016465499754345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377472463455652416543/100000000000000000000)
  centralHi := (11796014482989138017/3125000000000000000)
  directionLo := (15230769151491526553/4000000000000000000)
  directionHi := (190384614393644081913/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree059.table
  base := (-315023620975440262839466187038908032093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-12479890499367775662107249119918800000000000)
      constant := (181435278397103804783559395983934754515747032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree059.table
  base := (-504046896656495915640662584789094218529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1390192567824434727424267811105700000000000)
      constant := (20262904416478946113570181993263280703942715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15230769151491526553/4000000000000000000)
  centralHi := (190384614393644081913/50000000000000000000)
  directionLo := (76807538826668191987/20000000000000000000)
  directionHi := (6000588970833452499/1562500000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree060.table
  base := (-1990906395059847330157329342564011461371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1410161662891029044954996008753200000000000)
      constant := (20869083075983884793539976504487387621774757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree060.table
  base := (-49773633974558834541628164237716540079/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-471253232679387718740597960734400000000000)
      constant := (6992016169463818983315133543753904722365240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76807538826668191987/20000000000000000000)
  centralHi := (6000588970833452499/1562500000000000000)
  directionLo := (77455715202750763519/20000000000000000000)
  directionHi := (96819644003438454399/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree061.table
  base := (-286630579043141719635004866405580921693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-1173001766606431558825698094330800000000000)
      constant := (17665580596533942857389069821924046575571445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree061.table
  base := (-143318625931527812329184052385189620203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1437326828251891585019319953300700000000000)
      constant := (21701826405165313560559949965561968675333010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77455715202750763519/20000000000000000000)
  centralHi := (96819644003438454399/25000000000000000000)
  directionLo := (12202892537927844921/3125000000000000000)
  directionHi := (390492561213691037473/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree062.table
  base := (-26466717678302137808775827254256264119/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-13114583899322232889570393996498800000000000)
      constant := (200934193101420964588395066920061148465813024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree062.table
  base := (-846963541901903386269595245559635138947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1460893958465620013816846024398200000000000)
      constant := (22440237896999034509168687361030757040414749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12202892537927844921/3125000000000000000)
  centralHi := (390492561213691037473/100000000000000000000)
  directionLo := (196840154241465421489/50000000000000000000)
  directionHi := (393680308482930842979/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree063.table
  base := (-11612902308893440432153950942216568617/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-493561050591619208594744776124400000000000)
      constant := (7691117247663786830604640267779912354904260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree063.table
  base := (-232282527378569084164936020626597857973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-44983669353919649776193093802900000000000)
      constant := (702766145706412744806785358279704652142027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196840154241465421489/50000000000000000000)
  centralHi := (393680308482930842979/100000000000000000000)
  directionLo := (396842450112387722713/100000000000000000000)
  directionHi := (198421225056193861357/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree064.table
  base := (205436653072722112672185331553554861029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-13537712832625204374545823914218800000000000)
      constant := (214499302964882203888952856303826011587451226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree064.table
  base := (20542616418919953131934710177782436101/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1508028218893076871411898166593200000000000)
      constant := (23954960992059153020152984734896536407826660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396842450112387722713/100000000000000000000)
  centralHi := (198421225056193861357/50000000000000000000)
  directionLo := (399979593398451124913/100000000000000000000)
  directionHi := (199989796699225562457/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree065.table
  base := (1082455270762213994027524974169810287121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-13749277299276690117033538873078800000000000)
      constant := (221451603800611732136955736854300433655274937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree065.table
  base := (54121864560228912821321837396886131443/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1531595349106805300209424237690700000000000)
      constant := (24731272325014205881431300759620976096752380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399979593398451124913/100000000000000000000)
  centralHi := (199989796699225562457/50000000000000000000)
  directionLo := (403092322004745750199/100000000000000000000)
  directionHi := (2015461610023728751/500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree066.table
  base := (445621160680184894306995488989809578721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-141018603696244200601224786181200000000000)
      constant := (2308253204467072464616575186867077714944652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree066.table
  base := (891234614865145637617931113211390332363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-47126135736985870575968191175400000000000)
      constant := (773339900116411509519215294777647780664726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403092322004745750199/100000000000000000000)
  centralHi := (2015461610023728751/500000000000000000)
  directionLo := (406181197229961622413/100000000000000000000)
  directionHi := (203090598614980811207/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree067.table
  base := (502191746353703930389885669110570331857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-14172406232579661602008968790798800000000000)
      constant := (235695692490762536576278571201358796942807645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree067.table
  base := (2510945516439529565319226965466682520561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1578729609534262157804476379885700000000000)
      constant := (26321794041833246535987721097793781773178513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406181197229961622413/100000000000000000000)
  centralHi := (203090598614980811207/50000000000000000000)
  directionLo := (51155844898694178229/12500000000000000000)
  directionHi := (409246759189553425833/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree068.table
  base := (326787527834238542343142889109893143533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-14383970699231147344496683749658800000000000)
      constant := (242987478875088558742624770689054782636293010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree068.table
  base := (1633931972640125009207591474165374204649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1602296739747990586602002450983200000000000)
      constant := (27136004266189488624419525385462814697506834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51155844898694178229/12500000000000000000)
  centralHi := (409246759189553425833/100000000000000000000)
  directionLo := (103072381979588644687/25000000000000000000)
  directionHi := (412289527918354578749/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree069.table
  base := (4053232383529999421791244554301236764039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1621726129542514787442710967613200000000000)
      constant := (27821380647915697363058263163172740813213287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree069.table
  base := (202661133150032472207267140400444886439/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-541954623320573005133176174026900000000000)
      constant := (9320949105250998858049010269186091625016580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103072381979588644687/25000000000000000000)
  centralHi := (412289527918354578749/100000000000000000000)
  directionLo := (207655002200240187143/50000000000000000000)
  directionHi := (415310004400480374287/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree070.table
  base := (2433514225316011472227495677794638249773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-14807099632534118829472113667378800000000000)
      constant := (257910532885000985556312920997926015120365162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree070.table
  base := (4867020111878353673503637686574715646733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1649431000175447444197054593178200000000000)
      constant := (28802323139118932037593037091768590616342189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207655002200240187143/50000000000000000000)
  centralHi := (415310004400480374287/100000000000000000000)
  directionLo := (418308671532296083817/100000000000000000000)
  directionHi := (209154335766148041909/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree071.table
  base := (2854631068182442606813478480603499973861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-15018664099185604571959828626238800000000000)
      constant := (265541799637412466087985101714043278984473434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree071.table
  base := (5709254981914263847290603608555618073549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1672998130389175872994580664275700000000000)
      constant := (29654431693057324752403961926903166646427117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418308671532296083817/100000000000000000000)
  centralHi := (209154335766148041909/50000000000000000000)
  directionLo := (3291296836122588963/781250000000000000)
  directionHi := (84257199004738277453/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree072.table
  base := (32899661550410706537853246721276329337/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-51280230861404344493089372340400000000000)
      constant := (920155642264894692662576338333055265867400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree072.table
  base := (6579926170895936076298492607118453708173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-565521753534301433930702245124400000000000)
      constant := (10173057647065054690078649876685502990789903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3291296836122588963/781250000000000000)
  centralHi := (84257199004738277453/20000000000000000000)
  directionLo := (53030303030303030303/12500000000000000000)
  directionHi := (16969696969696969697/4000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree073.table
  base := (7479038019670957341831121549177117402799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-15441793032488576056935258543958800000000000)
      constant := (281143810948007246791030014064748003868631303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree073.table
  base := (7479032751009766503040674925712966863271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1720132390816632730589632806470700000000000)
      constant := (31396546852914601063791941419262459156487943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53030303030303030303/12500000000000000000)
  centralHi := (16969696969696969697/4000000000000000000)
  directionLo := (106794598251467177371/25000000000000000000)
  directionHi := (85435678601173741897/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree074.table
  base := (8406578463009987898717188941652136250767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-15653357499140061799422973502818800000000000)
      constant := (289114554985182995709665344617141884466477799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree074.table
  base := (1050821742613433885400515087082399693271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-158518138275487378126105352506200000000000)
      constant := (2935141218402831123600873391717052592638504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106794598251467177371/25000000000000000000)
  centralHi := (85435678601173741897/20000000000000000000)
  directionLo := (215047160162058271833/50000000000000000000)
  directionHi := (430094320324116543667/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree075.table
  base := (2340638241016134943632315868653017999391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1762769107310171949101187606853200000000000)
      constant := (33022050851490962955021376276902198375919612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree075.table
  base := (9362549082319015183332836844641182245883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-589088883748029862728228316221900000000000)
      constant := (11063064189340625604928299842482146754704713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215047160162058271833/50000000000000000000)
  centralHi := (430094320324116543667/100000000000000000000)
  directionLo := (432990611098036532509/100000000000000000000)
  directionHi := (43299061109803653251/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree076.table
  base := (10346960952851586739758458109314630593959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-16076486432443033284398403420538800000000000)
      constant := (305395518813429300657447000239175245286405823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree076.table
  base := (10346957620458316360440428975075187689057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1790833781457818016982211019763200000000000)
      constant := (34104464331378863708699267059917781193738881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432990611098036532509/100000000000000000000)
  centralHi := (43299061109803653251/10000000000000000000)
  directionLo := (108966914193896048363/25000000000000000000)
  directionHi := (435867656775584193453/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree077.table
  base := (5679900974318378265651776011147061005139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-1480731899917683547898738034490800000000000)
      constant := (28518703481130617212208011206703541294277506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree077.table
  base := (11359799087595486895430301954144579844643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-164945537424686040525430644623700000000000)
      constant := (3184760788824274249692956569716877489533929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108966914193896048363/25000000000000000000)
  centralHi := (435867656775584193453/100000000000000000000)
  directionLo := (87745167193874743609/20000000000000000000)
  directionHi := (219362917984686859023/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree078.table
  base := (12401075545832642087789366065945140014501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1833290596194000529930425926473200000000000)
      constant := (35792123997775741414276369709885789620478533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree078.table
  base := (387533534039838387700784640461121597381/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-612656013961758291525754387319400000000000)
      constant := (11990968530689765960650904229291989802278112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87745167193874743609/20000000000000000000)
  centralHi := (219362917984686859023/50000000000000000000)
  directionLo := (441565515038270580211/100000000000000000000)
  directionHi := (110391378759567645053/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree079.table
  base := (538831256086264821873829699548441201187/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-16711179832397490511861548297118800000000000)
      constant := (330665651774406011849920675732662375918813475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree079.table
  base := (3367694823186278577055465008459796209533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1861535172099003303374789233055700000000000)
      constant := (36926075065404916637378139700307424349658356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441565515038270580211/100000000000000000000)
  centralHi := (110391378759567645053/25000000000000000000)
  directionLo := (88877409727106811121/20000000000000000000)
  directionHi := (222193524317767027803/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree080.table
  base := (7284459614340009066584691943284133032349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-16922744299048976254349263255978800000000000)
      constant := (339315345589897990587323088975814775021215306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree080.table
  base := (7284458708620538045996143636242658747499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1885102302312731732172315304153200000000000)
      constant := (37891877087808619152107470417316015477334934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88877409727106811121/20000000000000000000)
  centralHi := (222193524317767027803/50000000000000000000)
  directionLo := (223595390112915710343/50000000000000000000)
  directionHi := (447190780225831420687/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree081.table
  base := (15695488781461583609798294746586336743609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-634604028359276370253221415364400000000000)
      constant := (12891785087185446567530253868558849704179699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree081.table
  base := (1961935903226882084395504404539493479047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-636223144175486720323280458416900000000000)
      constant := (12956770550487044247471939041582419176156136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223595390112915710343/50000000000000000000)
  centralHi := (447190780225831420687/100000000000000000000)
  directionLo := (449977042573257515527/100000000000000000000)
  directionHi := (56247130321657189441/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree082.table
  base := (4212622463627250849834774814485208673449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-17345873232351947739324693173698800000000000)
      constant := (356954207005553494925416139542670027904057412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree082.table
  base := (4212622129616913391429187086014841748579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1932236562740188589767367446348200000000000)
      constant := (39861378749762477126066508088419184110812428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449977042573257515527/100000000000000000000)
  centralHi := (56247130321657189441/12500000000000000000)
  directionLo := (226373079101161317199/50000000000000000000)
  directionHi := (452746158202322634399/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree083.table
  base := (3606784454770879644330921738712299601377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-1596130699909403043801128012050800000000000)
      constant := (33267579499351713022492745381692560446185895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree083.table
  base := (3606784225273522148115469532908940887497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1955803692953917018564893517445700000000000)
      constant := (40865078377141220854298131703603156496437005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226373079101161317199/50000000000000000000)
  centralHi := (452746158202322634399/100000000000000000000)
  directionLo := (455498439833716557891/100000000000000000000)
  directionHi := (113874609958429139473/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree084.table
  base := (2405723236570607327757219491473184777213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-1974333573961657691588902565713200000000000)
      constant := (41671744419146003131254108275977720781184232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree084.table
  base := (19245784906985683544032299710913759291501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-659790274389215149120806529514400000000000)
      constant := (13960470176297966284490713788410951352206511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455498439833716557891/100000000000000000000)
  centralHi := (113874609958429139473/25000000000000000000)
  directionLo := (229117095398257684933/50000000000000000000)
  directionHi := (458234190796515369867/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree085.table
  base := (20486080586538320455568108418653474305229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-17980566632306404966787838050278800000000000)
      constant := (384261182807030736675957276929688081868653013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree085.table
  base := (20486079739995892492786635157026510061031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-182085268489215806923631423603700000000000)
      constant := (3900943200095432163694527553231423280183093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229117095398257684933/50000000000000000000)
  centralHi := (458234190796515369867/100000000000000000000)
  directionLo := (460953705418369101031/100000000000000000000)
  directionHi := (57619213177296137629/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree086.table
  base := (4350961250191890788771028628502421421007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-18192131098957890709275553009138800000000000)
      constant := (393589823565888815787266941201822895810195395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree086.table
  base := (21754805523821486772248213680676810921529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2026505083595102304957471730738200000000000)
      constant := (43951972390256752918919576233908759760410457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460953705418369101031/100000000000000000000)
  centralHi := (57619213177296137629/12500000000000000000)
  directionLo := (28978579337193184701/6250000000000000000)
  directionHi := (463657269395090955217/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree087.table
  base := (4610392559462113860952582268039530828361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2044855062845486272418140885333200000000000)
      constant := (44781291335844279072212850057504922586679565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree087.table
  base := (23051962172722871286765790398858619881563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-683357404602943577918332600611900000000000)
      constant := (15002067364561829856718323243060988568697193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28978579337193184701/6250000000000000000)
  centralHi := (463657269395090955217/100000000000000000000)
  directionLo := (466345160140961788871/100000000000000000000)
  directionHi := (58293145017620223609/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree088.table
  base := (487551003016990249567181057838952288007/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-1692296366569169290386452993350800000000000)
      constant := (37507870741360127682554863083752985588809450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree088.table
  base := (487550992286827712834098101369846570071/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-188512667638414469322956715721200000000000)
      constant := (4188460391722557087393004216667876985510650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466345160140961788871/100000000000000000000)
  centralHi := (58293145017620223609/12500000000000000000)
  directionLo := (117254411780241408807/25000000000000000000)
  directionHi := (469017647120965635229/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree089.table
  base := (1029262729939228088688096454550072905799/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-18826824498912347936738697885718800000000000)
      constant := (422254691944238106731340447952137491325557575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree089.table
  base := (25731567787626716147642315187717074078941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2097206474236287591350049944030700000000000)
      constant := (47152559034030007740672839193838394694605053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117254411780241408807/25000000000000000000)
  centralHi := (469017647120965635229/100000000000000000000)
  directionLo := (471674992166082504987/100000000000000000000)
  directionHi := (117918748041520626247/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree090.table
  base := (2711401703695731346685462316259059392293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-705125517243104951082459734984400000000000)
      constant := (16001331976837567084387345134184496533152230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree090.table
  base := (27114016641087333682158722073539064241409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-706924534816672006715858671709400000000000)
      constant := (16081562089077302815721503768039804706655499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471674992166082504987/100000000000000000000)
  centralHi := (117918748041520626247/25000000000000000000)
  directionLo := (237158724886341331437/50000000000000000000)
  directionHi := (3794539598181461303/800000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree091.table
  base := (5704979294272505989069916536972288708157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-19249953432215319421714127803438800000000000)
      constant := (441930392432749723713713172569544648731613145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree091.table
  base := (28524896131313062802033571450937727941521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2144340734663744448945102086225700000000000)
      constant := (49349446007121294291171784423114026272070193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237158724886341331437/50000000000000000000)
  centralHi := (3794539598181461303/800000000000000000)
  directionLo := (476945267386991364943/100000000000000000000)
  directionHi := (29809079211686960309/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree092.table
  base := (29964206513826093299639691110045136681183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-19461517898866805164201842762298800000000000)
      constant := (451937979107396877306249872942133005594311351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree092.table
  base := (29964206221727017434707383482332605736537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2167907864877472877742628157323200000000000)
      constant := (50466838252491128032300195716182075989305721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476945267386991364943/100000000000000000000)
  centralHi := (29809079211686960309/6250000000000000000)
  directionLo := (59944835709440501229/12500000000000000000)
  directionHi := (479558685675524009833/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree093.table
  base := (31431947132439334621908309366312825360147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2185898040613143434076617524573200000000000)
      constant := (51339858154342099710049653104045923236884851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree093.table
  base := (1257277875261237940699186660451676359243/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-730491665030400435513384742806900000000000)
      constant := (17198954334108355817160209652887104748791825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59944835709440501229/12500000000000000000)
  centralHi := (479558685675524009833/100000000000000000000)
  directionLo := (60269742347791029829/12500000000000000000)
  directionHi := (482157938782328238633/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree094.table
  base := (32928118300337708670215573687176409396279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-1807695166560888786288842970910800000000000)
      constant := (42935693206347001275404368001248963053699533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree094.table
  base := (32928118084813757327146563518643110361319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2215042125304929735337680299518200000000000)
      constant := (52739520255768046290847356868919047641923527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60269742347791029829/12500000000000000000)
  centralHi := (482157938782328238633/100000000000000000000)
  directionLo := (484743254573811200753/100000000000000000000)
  directionHi := (242371627286905600377/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree095.table
  base := (4306589999365593332136642606158932661387/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-20096211298821262391664987638878800000000000)
      constant := (482639684742900075993375285236769624003455512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree095.table
  base := (17226359904898858190484332605192963837067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2238609255518658164135206370615700000000000)
      constant := (53894810012101399543469978940253266863246422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484743254573811200753/100000000000000000000)
  centralHi := (242371627286905600377/50000000000000000000)
  directionLo := (487314854871876527149/100000000000000000000)
  directionHi := (9746297097437530543/2000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree096.table
  base := (7201150439443090751814955317761357174969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2256419529496972014905855844193200000000000)
      constant := (54788877978076615535517679781017823933869885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree096.table
  base := (4500719004775119831795289667185069224669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-68550799567648078573719164900400000000000)
      constant := (1668567644567328048410219229771080553797352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487314854871876527149/100000000000000000000)
  centralHi := (9746297097437530543/2000000000000000000)
  directionLo := (489872955676046103219/100000000000000000000)
  directionHi := (24493647783802305161/5000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree097.table
  base := (1879360744564031534391081995079746906491/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-20519340232124233876640417556598800000000000)
      constant := (503673276444454433319662910612667296624556540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree097.table
  base := (37587214754698171168775030285550707986897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2285743515946115021730258512810700000000000)
      constant := (56243287031123589124756891638221804613567601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489872955676046103219/100000000000000000000)
  centralHi := (24493647783802305161/5000000000000000000)
  directionLo := (123104441843799034557/25000000000000000000)
  directionHi := (492417767375196138229/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree098.table
  base := (39197108063776501570058172915239596941521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-20730904698775719619128132515458800000000000)
      constant := (514359808664231655059023822299188560291631737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree098.table
  base := (39197107946464265535222253481932276294933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2309310646159843450527784583908200000000000)
      constant := (57436474292883462208292459938683790117732789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123104441843799034557/25000000000000000000)
  centralHi := (492417767375196138229/100000000000000000000)
  directionLo := (247474747474747474747/50000000000000000000)
  directionHi := (98989898989898989899/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree099.table
  base := (20417715851773236068851361633463825932181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-70513364193357593810154368600400000000000)
      constant := (1768213799524268338518927953996527651864362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree099.table
  base := (2041771580139409159808525581809175328521/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-70693265950714299373494262272900000000000)
      constant := (1777039213807514542901373781795364756570420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247474747474747474747/50000000000000000000)
  centralHi := (98989898989898989899/20000000000000000000)
  directionLo := (497468338163091013363/100000000000000000000)
  directionHi := (124367084540772753341/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree100.table
  base := (10625546450320974314388040017668889928399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-21154033632078691104103562433178800000000000)
      constant := (536072345825118484158394920852870641234938012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree100.table
  base := (10625546428686499963383050094977873394771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2356444906587300308122836726103200000000000)
      constant := (59860746319122652745278625275754579288109772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497468338163091013363/100000000000000000000)
  centralHi := (124367084540772753341/25000000000000000000)
  directionLo := (249987245874031953071/50000000000000000000)
  directionHi := (499974491748063906143/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree101.table
  base := (2209868517462323366452577729279783841677/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-21365598098730176846591277392038800000000000)
      constant := (547098350761164551962478964010850716019561380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree101.table
  base := (11049342568731045715074307640613620161407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2380012036801028736920362797200700000000000)
      constant := (61091831083062834119540998426234579111305724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249987245874031953071/50000000000000000000)
  centralHi := (499974491748063906143/100000000000000000000)
  directionLo := (502468145580117517569/100000000000000000000)
  directionHi := (50246814558011751757/10000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree102.table
  base := (1148024633525357026662892764606416173487/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2397462507264629176564332483433200000000000)
      constant := (62026390362771021030058358725706869349002840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree102.table
  base := (4592098527718527815302047699572308131009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-801193055671585721905962956099400000000000)
      constant := (20778516115755329351479588373160028894410990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502468145580117517569/100000000000000000000)
  centralHi := (50246814558011751757/10000000000000000000)
  directionLo := (63118685605808017659/12500000000000000000)
  directionHi := (504949484846464141273/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree103.table
  base := (9534606154256980238945068228219970706551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-21788727032033148331566707309758800000000000)
      constant := (569489833334867572211793586197513056499228235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree103.table
  base := (23836515358234751127553382148922944151873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2427146297228485594515414939395700000000000)
      constant := (63591898111565141695244284567889345564023618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63118685605808017659/12500000000000000000)
  centralHi := (504949484846464141273/100000000000000000000)
  directionLo := (507418690206319526409/100000000000000000000)
  directionHi := (50741869020631952641/10000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree104.table
  base := (49453506635699726088044396482624017258427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-22000291498684634074054422268618800000000000)
      constant := (580855310969655196103470130226574533125752819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree104.table
  base := (49453506588626725692282604695228799543037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2450713427442214023312941010493200000000000)
      constant := (64860880375823340769306531674933750384920221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507418690206319526409/100000000000000000000)
  centralHi := (50741869020631952641/10000000000000000000)
  directionLo := (509875937944402526299/100000000000000000000)
  directionHi := (5098759379444025263/1000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree105.table
  base := (51262412930696884935295850650626080729889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-224362181468041614308506436641200000000000)
      constant := (5983171173416607932471063473827878242189667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree105.table
  base := (51262412890274186749778616411211994262423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-824760185885314150703489027196900000000000)
      constant := (22047498379976318046679372280661175686886653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509875937944402526299/100000000000000000000)
  centralHi := (5098759379444025263/1000000000000000000)
  directionLo := (64040175014726054303/12500000000000000000)
  directionHi := (20492856004712337377/4000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree106.table
  base := (13274937413346650562204172341302031526777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-22423420431987605559029852186338800000000000)
      constant := (603925738929776276525453132003539613453811076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree106.table
  base := (53099749618675993951112967512136349661567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2497847687869670880907993152688200000000000)
      constant := (67436742403791697388715139615227924538831711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64040175014726054303/12500000000000000000)
  centralHi := (20492856004712337377/4000000000000000000)
  directionLo := (128688811174150575499/25000000000000000000)
  directionHi := (514755244696602301997/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree107.table
  base := (1374137920036140024247020487296084481971/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-22634984898639091301517567145198800000000000)
      constant := (615630689253561456449482024849359083645815480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree107.table
  base := (27482758385820541499297031861056529756987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-229219528916672664518683565798700000000000)
      constant := (6249420197030842308501252489414782928541922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128688811174150575499/25000000000000000000)
  centralHi := (514755244696602301997/100000000000000000000)
  directionLo := (103435527139691468889/20000000000000000000)
  directionHi := (258588817849228672223/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree108.table
  base := (56859714373027640121556295070921933278871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-846168495010762112740936374224400000000000)
      constant := (23238844338483384870984191648015341266067581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree108.table
  base := (3553732146714800428549121551643508725853/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-848327316099042579501015098294400000000000)
      constant := (23354378143504826934088214486632557535750128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103435527139691468889/20000000000000000000)
  centralHi := (258588817849228672223/50000000000000000000)
  directionLo := (519588733317643839011/100000000000000000000)
  directionHi := (129897183329410959753/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree109.table
  base := (29391171183343864053525220481720669184243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-23058113831942062786492997062918800000000000)
      constant := (639380062585816919222479156428421277495440342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree109.table
  base := (29391171172357885513784390585314166588449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2568549078510856167300571365980700000000000)
      constant := (71395279193272879596529783465649216244837634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519588733317643839011/100000000000000000000)
  centralHi := (129897183329410959753/25000000000000000000)
  directionLo := (260994347024327787951/50000000000000000000)
  directionHi := (521988694048655575903/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree110.table
  base := (60733400781317929113392832982676756142991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2115425299872140775361882911070800000000000)
      constant := (59220407781229907511886159514720272415860757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree110.table
  base := (30366700381226946169054428229872478361921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-235646928065871326918008857916200000000000)
      constant := (6612732405052787911964153160279109870171526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260994347024327787951/50000000000000000000)
  centralHi := (521988694048655575903/100000000000000000000)
  directionLo := (262188835402371922429/50000000000000000000)
  directionHi := (524377670804743844859/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree111.table
  base := (31356444808046499199056219785509790306961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2609026973916114919052047442293200000000000)
      constant := (73731340684660276005873896980478846160259426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree111.table
  base := (62712889599897969236997830090611813685771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-871894446312771008298541169391900000000000)
      constant := (24699155405804329152098624037420173700543481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262188835402371922429/50000000000000000000)
  centralHi := (524377670804743844859/100000000000000000000)
  directionLo := (26337790651580651019/5000000000000000000)
  directionHi := (526755813031613020381/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree112.table
  base := (64720808870424351552519100420084702359563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-23692807231896520013956141939498800000000000)
      constant := (675852804290882613919450133303990756600790211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree112.table
  base := (32360404428260656751003985983986781856773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2639250469152041453693149579273200000000000)
      constant := (75467508478752460159266830420076727602547018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26337790651580651019/5000000000000000000)
  centralHi := (526755813031613020381/100000000000000000000)
  directionLo := (529123266816516963617/100000000000000000000)
  directionHi := (264561633408258481809/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree113.table
  base := (33378579271960550382629481054271679741901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-23904371698548005756443856898358800000000000)
      constant := (688236699980233278550530841634831777766689194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree113.table
  base := (66757158531986214842813024299920747543319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2662817599365769882490675650370700000000000)
      constant := (76850183239587940700937793179385815918929527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529123266816516963617/100000000000000000000)
  centralHi := (264561633408258481809/50000000000000000000)
  directionLo := (16608755468530675173/3125000000000000000)
  directionHi := (531480174992981605537/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree114.table
  base := (8602742329544635509005625631400279131759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2679548462799943499881285761913200000000000)
      constant := (77859305914436367538079328111114473690784376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree114.table
  base := (4301371164132012337458096831480181556087/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-895461576526499437096067240489400000000000)
      constant := (26081830166637824459308668981118786953871312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16608755468530675173/3125000000000000000)
  centralHi := (531480174992981605537/100000000000000000000)
  directionLo := (33364167327585383763/6250000000000000000)
  directionHi := (533826677241366140209/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree115.table
  base := (70915149147642976983163484873661964993953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-24327500631850977241419286816078800000000000)
      constant := (713343964039938172422554485320389603603204041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree115.table
  base := (7091514913884918587218160466088980696493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2709951859793226740085727792565700000000000)
      constant := (79653430259727405705352065615482144879842690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33364167327585383763/6250000000000000000)
  centralHi := (533826677241366140209/100000000000000000000)
  directionLo := (536162910185463170503/100000000000000000000)
  directionHi := (67020363773182896313/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree116.table
  base := (9129598759725339286771471421706724598161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2230824099863860271264272888630800000000000)
      constant := (66006121128206634629484816129621452513202776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree116.table
  base := (73036790070254833429606782428517725572047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2733518990006955168883253863663200000000000)
      constant := (81074002519031640237767809733643384943877551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536162910185463170503/100000000000000000000)
  centralHi := (67020363773182896313/12500000000000000000)
  directionLo := (538489007485326848481/100000000000000000000)
  directionHi := (269244503742663424241/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree117.table
  base := (37593430713476783579685790863840817332819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-916689983894590693570174693844400000000000)
      constant := (27366809568183946773365816271029297981322018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree117.table
  base := (75186861420475377372058558305511015415719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-919028706740227865893593311586900000000000)
      constant := (27502402425943667602029401331968414919572909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538489007485326848481/100000000000000000000)
  centralHi := (269244503742663424241/50000000000000000000)
  directionLo := (135201274981626870493/25000000000000000000)
  directionHi := (540805099926507481973/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree118.table
  base := (9670670399411164986827151316135310075953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-24962194031805434468882431692658800000000000)
      constant := (751853541832076472233995396490475896740464328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree118.table
  base := (9670670398716185621618770864953386662691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-252786659130401093316209636896200000000000)
      constant := (7632094957830246311848716831362156279904584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135201274981626870493/25000000000000000000)
  centralHi := (540805099926507481973/100000000000000000000)
  directionLo := (108622263101172236829/20000000000000000000)
  directionHi := (271555657752930592073/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree119.table
  base := (9946536922883259402876911770390997570217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-25173758498456920211370146651518800000000000)
      constant := (764916382883678771492450719950316210226835592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree119.table
  base := (79572295378294633629064704154930875421063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2804220380648140455275832076955700000000000)
      constant := (85411514293945916864604695345052950138895079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108622263101172236829/20000000000000000000)
  centralHi := (271555657752930592073/50000000000000000000)
  directionLo := (136351944878523468969/25000000000000000000)
  directionHi := (545407779514093875877/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree120.table
  base := (81807657990590288105487776327340287490931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2820591440567600661539762401153200000000000)
      constant := (86454709055096053086626314108386229487200723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree120.table
  base := (40903828993247819354484186928930961666259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-942595836953956294691119382684400000000000)
      constant := (28960872183760448005352439774348481156657698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136351944878523468969/25000000000000000000)
  centralHi := (545407779514093875877/100000000000000000000)
  directionLo := (547694614615190266591/100000000000000000000)
  directionHi := (17115456706724695831/3125000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree121.table
  base := (8407145101820868887034232834568077501759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2326989766523626517849597869930800000000000)
      constant := (71943776151703324545732826904470180925474930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree121.table
  base := (84071451014695001193657010920466664379477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-259214058279599755715534929013700000000000)
      constant := (8033304664377359401551510875490793743138431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547694614615190266591/100000000000000000000)
  centralHi := (17115456706724695831/3125000000000000000)
  directionLo := (137492985230717574189/25000000000000000000)
  directionHi := (549971940922870296757/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree122.table
  base := (86363674466299807731353297991914145670341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-25808451898411377438833291528098800000000000)
      constant := (804783851402407471636214508160212101264091277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree122.table
  base := (43181837231642398488197244623878506750077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2874921771289325741668410290248200000000000)
      constant := (89862718564567683572110304105978206445505082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137492985230717574189/25000000000000000000)
  centralHi := (549971940922870296757/100000000000000000000)
  directionLo := (552239876074207886453/100000000000000000000)
  directionHi := (276119938037103943227/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree123.table
  base := (110855410419083570457713422406945721819/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2891112929451429242369000720773200000000000)
      constant := (90922146966332992949706569916496967056021600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree123.table
  base := (44342164166339935947307474749079351149109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-966162967167684723488645453781900000000000)
      constant := (30457239440181741464607899797170639475280398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552239876074207886453/100000000000000000000)
  centralHi := (276119938037103943227/50000000000000000000)
  directionLo := (554498535300539664339/100000000000000000000)
  directionHi := (27724926765026983217/5000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree124.table
  base := (22758353156382939801010186036199643295421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-26231580831714348923808721445818800000000000)
      constant := (831927951552630276291981049725416376234960148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree124.table
  base := (91033412623312142361683907385888891593101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2922056031716782599263462432443200000000000)
      constant := (92893350576097829123847867505569033422572333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554498535300539664339/100000000000000000000)
  centralHi := (27724926765026983217/5000000000000000000)
  directionLo := (556748031495784617553/100000000000000000000)
  directionHi := (278374015747892308777/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree125.table
  base := (18682185467506031689875199789541664562997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-26443145298365834666296436404678800000000000)
      constant := (845669737969436876604790836233569371876050545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree125.table
  base := (11676365916953228978536394291921348985273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2945623161930511028060988503540700000000000)
      constant := (94427615331240157136055571565155517382112072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556748031495784617553/100000000000000000000)
  centralHi := (278374015747892308777/50000000000000000000)
  directionLo := (279494237641144637929/50000000000000000000)
  directionHi := (558988475282289275859/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree126.table
  base := (11977109058963405437136901638334543717677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-987211472778419274399413013464400000000000)
      constant := (31834247479538850323558494291567839847155576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree126.table
  base := (95816872470073499060138541919469266458091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-989730097381413152286171524879400000000000)
      constant := (31991504195329047623238324224058636931039001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279494237641144637929/50000000000000000000)
  centralHi := (558988475282289275859/100000000000000000000)
  directionLo := (280609987537153547477/50000000000000000000)
  directionHi := (112243995014861418991/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree127.table
  base := (24562812007128569499501955892294672873713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2442388566515346013751987847490800000000000)
      constant := (79408434862463686180921543765009424670361004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree127.table
  base := (98251248027112736071319552692539477751701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-2992757422357967885656040645735700000000000)
      constant := (97534042340353886861291155750923934015806133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280609987537153547477/50000000000000000000)
  centralHi := (112243995014861418991/20000000000000000000)
  directionLo := (563442637139215108921/100000000000000000000)
  directionHi := (281721318569607554461/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree128.table
  base := (12589256751050714627353824712240885157019/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-27077838698320291893759581281258800000000000)
      constant := (887574042588226617521778622768610743133077144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree128.table
  base := (50357027003601716047495130432889409353457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3016324552571696314453566716833200000000000)
      constant := (99106204594355565455478271250369101017328162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563442637139215108921/100000000000000000000)
  centralHi := (281721318569607554461/50000000000000000000)
  directionLo := (113131313131313131313/20000000000000000000)
  directionHi := (282828282828282828283/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree129.table
  base := (20641058082367364605889679899682830419933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3032155907219086404027477360013200000000000)
      constant := (100196495472340264476062230504720467019288945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree129.table
  base := (25801322602701378926869395329093786608243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-92117929781376507371245235997900000000000)
      constant := (3051242404485071402887730526104806396432972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113131313131313131313/20000000000000000000)
  centralHi := (282828282828282828283/50000000000000000000)
  directionLo := (567861862775066029209/100000000000000000000)
  directionHi := (56786186277506602921/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree130.table
  base := (52862478619630851639325517808136038113717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-27500967631623263378735011198978800000000000)
      constant := (916076033475742706131371909310476806639547898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree130.table
  base := (52862478619188550287480550758080925077701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3063458812999153172048618859028200000000000)
      constant := (102288426601324377131725590470762966055128266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567861862775066029209/100000000000000000000)
  centralHi := (56786186277506602921/10000000000000000000)
  directionLo := (142514657166893554461/25000000000000000000)
  directionHi := (114011725733514843569/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree131.table
  base := (108273054491131702860891012899949448676933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-27712532098274749121222726157838800000000000)
      constant := (930496765262401644555266521606577786257049101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree131.table
  base := (54136527245186485812214484559135688449293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3087025943212881600846144930125700000000000)
      constant := (103898486354321635867360329450835536687653338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142514657166893554461/25000000000000000000)
  centralHi := (114011725733514843569/20000000000000000000)
  directionLo := (572246961584194536909/100000000000000000000)
  directionHi := (57224696158419453691/10000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree132.table
  base := (55424791083947048873081382022419763385651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-282061581463901362259701425421200000000000)
      constant := (9545764187991636732518507655972918580313906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree132.table
  base := (110849582167243358058877409146867328902657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-94260396164442728171020333370400000000000)
      constant := (3197611472939817880784793931135567328902657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572246961584194536909/100000000000000000000)
  centralHi := (57224696158419453691/10000000000000000000)
  directionLo := (574426957903552752759/100000000000000000000)
  directionHi := (14360673947588818819/2500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree133.table
  base := (113454540269991040510551856366831265276961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-28135661031577720606198156075558800000000000)
      constant := (959677701522185201338666531807519285787257417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree133.table
  base := (56727270134716473900129485865898615305341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3134160203640338458441197072320700000000000)
      constant := (107156503359416114428763635454962489860152506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574426957903552752759/100000000000000000000)
  centralHi := (14360673947588818819/2500000000000000000)
  directionLo := (288299356091163215487/50000000000000000000)
  directionHi := (23063948487293057239/4000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree134.table
  base := (58043964398929359346703475580090696926631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-28347225498229206348685871034418800000000000)
      constant := (974437905995570686712455895609573073974418814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree134.table
  base := (116087928797380104872604249439730266526547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3157727333854066887238723143418200000000000)
      constant := (108804460611542474968749646188001923795376051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288299356091163215487/50000000000000000000)
  centralHi := (23063948487293057239/4000000000000000000)
  directionLo := (72345289650387815391/12500000000000000000)
  directionHi := (578762317203102523129/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree135.table
  base := (118749747751926691811116140955772565912687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1057732961662247855228651333084400000000000)
      constant := (36641158075239113771002504178857498225039557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree135.table
  base := (59374873875758128559373567931244498922749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1060431488022598438678749738171900000000000)
      constant := (36821683454469102934889916805040722726300478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72345289650387815391/12500000000000000000)
  centralHi := (578762317203102523129/100000000000000000000)
  directionLo := (580917864020630726393/100000000000000000000)
  directionHi := (290458932010315363197/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree136.table
  base := (24287999426523475648126689808337009715553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-28770354431532177833661300952138800000000000)
      constant := (1004297787629966814910457028382817259427596205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree136.table
  base := (60719998566132713317779780741481363663241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3204861594281523744833775285613200000000000)
      constant := (112138272615024608665720721842258570001773906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580917864020630726393/100000000000000000000)
  centralHi := (290458932010315363197/50000000000000000000)
  directionLo := (58306544200653785553/10000000000000000000)
  directionHi := (583065442006537855531/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree137.table
  base := (12415867694034566758698834201233764289539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-28981918898183663576149015910998800000000000)
      constant := (1019397464791226138205317893849109879939930830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree137.table
  base := (24831735388008775909786340526680359738337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3228428724495252173631301356710700000000000)
      constant := (113824127366408111334056936288375390606825605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58306544200653785553/10000000000000000000)
  centralHi := (583065442006537855531/100000000000000000000)
  directionLo := (292602569446282677153/50000000000000000000)
  directionHi := (585205138892565354307/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree138.table
  base := (126905787175518637885841676435195801566713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-294883670351870195137744756261200000000000)
      constant := (10450609086013686301800419026551187404700139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree138.table
  base := (12690578717525987534495443234965235854761/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1083998618236326867476275809269400000000000)
      constant := (38507538205857096457573130854551850944023710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292602569446282677153/50000000000000000000)
  centralHi := (585205138892565354307/100000000000000000000)
  directionLo := (58733704081238913099/10000000000000000000)
  directionHi := (587337040812389130991/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree139.table
  base := (16210165979816920020595035329078625303091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-29405047831486635061124445828718800000000000)
      constant := (1049936291802471756024415146326934013720144216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree139.table
  base := (32420331959578374756163811140328140439989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3275562984922709031226353498905700000000000)
      constant := (117233734368527345586741997967775795788078548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58733704081238913099/10000000000000000000)
  centralHi := (587337040812389130991/100000000000000000000)
  directionLo := (294730616171039059877/50000000000000000000)
  directionHi := (117892246468415623951/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree140.table
  base := (5299411957191471023208567725633776364881/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-29616612298138120803612160787578800000000000)
      constant := (1065375441652692684167310481607462789509241425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree140.table
  base := (26497059785919312387671472048856225833237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-299920919557857950911261779091200000000000)
      constant := (10814316965389928159153219890267343387498555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294730616171039059877/50000000000000000000)
  centralHi := (117892246468415623951/20000000000000000000)
  directionLo := (295788898269622668477/50000000000000000000)
  directionHi := (118315559307849067391/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree141.table
  base := (135317700449655632633494880787735995974499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3314241862754400727344430638493200000000000)
      constant := (120103083229570156067979006322226487867158467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree141.table
  base := (67658850224746279676006025713419830891283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1107565748450055296273801880366900000000000)
      constant := (40231290456623179069442015672027930029608226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295788898269622668477/50000000000000000000)
  centralHi := (118315559307849067391/20000000000000000000)
  directionLo := (14842170374523567729/2500000000000000000)
  directionHi := (593686814980942709161/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree142.table
  base := (69089266199258236954540692362637002775947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-30039741231441092288587590705298800000000000)
      constant := (1096593214042899156505507146832795979648912518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree142.table
  base := (27635706479675334932180753780530420562781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3346264375563894317618931712198200000000000)
      constant := (122442888620280709011708269513395744392858865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14842170374523567729/2500000000000000000)
  centralHi := (593686814980942709161/100000000000000000000)
  directionLo := (148947091950087147511/25000000000000000000)
  directionHi := (119157673560069718009/20000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree143.table
  base := (141067794776735663425489550170651277415403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2750118699826598002825027787650800000000000)
      constant := (101124712416645886360172541585021984490215881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree143.table
  base := (141067794776615821746217840862262430540689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-306348318707056613310587071208700000000000)
      constant := (11291321670048621210810109283196781041622067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148947091950087147511/25000000000000000000)
  centralHi := (119157673560069718009/20000000000000000000)
  directionLo := (119576506744458929583/20000000000000000000)
  directionHi := (149470633430573661979/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree144.table
  base := (71992743792335723542770529411961866537701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1128254450546076436057889652704400000000000)
      constant := (41787541358772392000523019561936761063829422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree144.table
  base := (1799818594807108978872243652381931037907/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1131132878663783725071327951464400000000000)
      constant := (41992940206881249271365025747530499313358160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119576506744458929583/20000000000000000000)
  centralHi := (149470633430573661979/25000000000000000000)
  directionLo := (59996939009767668737/10000000000000000000)
  directionHi := (599969390097676687371/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree145.table
  base := (18366451352834254987230732610593970677587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-30674434631395549516050735581878800000000000)
      constant := (1144268554354252672519735014253247274329946712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree145.table
  base := (7346580541129299207903606565719652433689/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3416965766205079604011509925490700000000000)
      constant := (127765735370619022950873847373763001856234740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59996939009767668737/10000000000000000000)
  centralHi := (599969390097676687371/100000000000000000000)
  directionLo := (301024506468395980209/50000000000000000000)
  directionHi := (602049012936791960419/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree146.table
  base := (149906164491085734646018254090506502787909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-30885999098047035258538450540738800000000000)
      constant := (1160386649585400676435471862106105231328008973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree146.table
  base := (74953082245505129684604777603437254544787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3440532896418808032809035996588200000000000)
      constant := (129565282620471965851825267808791283799955942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301024506468395980209/50000000000000000000)
  centralHi := (602049012936791960419/100000000000000000000)
  directionLo := (60412147694164361793/10000000000000000000)
  directionHi := (604121476941643617931/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree147.table
  base := (152909148590241027533860368101902512016107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3455284840522057889002907277733200000000000)
      constant := (130735322486710882348206811582233182896531531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree147.table
  base := (7645457429508816904600968523691308882149/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1154700008877512153868854022561900000000000)
      constant := (43792487456737874907953549855222881704072780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60412147694164361793/10000000000000000000)
  centralHi := (604121476941643617931/100000000000000000000)
  directionLo := (606186855537251145513/100000000000000000000)
  directionHi := (303093427768625572757/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree148.table
  base := (155940563120466757056489274354280042251763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-31309128031350006743513880458458800000000000)
      constant := (1192962312739341537647953110871523572548773611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree148.table
  base := (38985140780102828604250704794586629227203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3487667156846264890404088138783200000000000)
      constant := (133202274619854793671966533632477335057990796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606186855537251145513/100000000000000000000)
  centralHi := (303093427768625572757/50000000000000000000)
  directionLo := (9503831576593811143/1562500000000000000)
  directionHi := (608245220902003913153/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree149.table
  base := (159000408082082252958735941299852252115993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2865517499818317498727417765210800000000000)
      constant := (109947261878393300628360189057335210807131811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree149.table
  base := (159000408082034737343534031440266638901299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3511234287059993319201614209880700000000000)
      constant := (135039719369406017813122266303171780333742867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9503831576593811143/1562500000000000000)
  centralHi := (608245220902003913153/100000000000000000000)
  directionLo := (19071770124909166873/3125000000000000000)
  directionHi := (610296643997093339937/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree150.table
  base := (40522170868849873164936255951767019049469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3525806329405886469832145597353200000000000)
      constant := (136221178461049434024374908112613246514529908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree150.table
  base := (162088683475358772362273319473675287373189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1178267139091240582666380093659400000000000)
      constant := (45629932206292532869506545960272303161105079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19071770124909166873/3125000000000000000)
  centralHi := (610296643997093339937/100000000000000000000)
  directionLo := (19135662331095550907/3125000000000000000)
  directionHi := (24493647783802305161/4000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree151.table
  base := (165205389300723262960694293057486952790249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-31943821431304463970977025335038800000000000)
      constant := (1242674489200787857250139189060942424978703953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree151.table
  base := (20650673662586045948750715058491881284427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-323488049771586379708787850188700000000000)
      constant := (12613864215298145395092050417514698900826248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19135662331095550907/3125000000000000000)
  centralHi := (24493647783802305161/4000000000000000000)
  directionLo := (614378941307471558991/100000000000000000000)
  directionHi := (38398683831716972437/6250000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree152.table
  base := (16835052555835132522294814332441660467329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-32155385897955949713464740293898800000000000)
      constant := (1259471529816443595128582352872129331587967130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree152.table
  base := (6734021022332856909901582789908096588689/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3581935677701178605594192423173200000000000)
      constant := (140627848617621850716387691504419779685668425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614378941307471558991/100000000000000000000)
  centralHi := (38398683831716972437/6250000000000000000)
  directionLo := (77051243951476552691/12500000000000000000)
  directionHi := (616409951611812421529/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree153.table
  base := (171524092248574582516973024293443802023773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1198775939429905016887127972324400000000000)
      constant := (47273397333203648817282674074211081822261503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree153.table
  base := (171524092248548959569731466743573287244947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1201834269304969011463906164756900000000000)
      constant := (47505274455637985478965105465766949909694417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77051243951476552691/12500000000000000000)
  centralHi := (616409951611812421529/100000000000000000000)
  directionLo := (618434291877531868123/100000000000000000000)
  directionHi := (154608572969382967031/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree154.table
  base := (174726089371677247506652194189609996674763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-2961683166478083745312742746510800000000000)
      constant := (117582280340094276111405641649862669910218601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree154.table
  base := (21840761171456911561060734460595661479743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-329915448920785042108113142306200000000000)
      constant := (13128766419651390807617116053715370875513832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618434291877531868123/100000000000000000000)
  centralHi := (154608572969382967031/25000000000000000000)
  directionLo := (620452027391362165887/100000000000000000000)
  directionHi := (4847281463995016921/781250000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree155.table
  base := (1112228230799606312853860409290948663799/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-32790079297910406940927885170478800000000000)
      constant := (1310541597050141626494867635011169880503728480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree155.table
  base := (44489129231979549660448924879864664016721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3652637068342363891986770636465700000000000)
      constant := (146329670365385044702620337882414416900207172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620452027391362165887/100000000000000000000)
  centralHi := (4847281463995016921/781250000000000000)
  directionLo := (622463222381884161719/100000000000000000000)
  directionHi := (15561580559547104043/2500000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree156.table
  base := (181215374917625203738135331649233171504147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3666849307173543631490622236593200000000000)
      constant := (147532363102654763549501655661203894659636851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree156.table
  base := (22651921864701135805070359795593670672927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1225401399518697440261432235854400000000000)
      constant := (49418514204860716790317088098600343019217576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622463222381884161719/100000000000000000000)
  centralHi := (15561580559547104043/2500000000000000000)
  directionLo := (312233970021691555471/50000000000000000000)
  directionHi := (624467940043383110943/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree157.table
  base := (46125665835251742641815048537282422948937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-33213208231213378425903315088198800000000000)
      constant := (1345154096362369520756172191404513118463337156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree157.table
  base := (184502663340993162075177130299159070304557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3699771328769820749581822778660700000000000)
      constant := (150194047363765367693063916527620130570050381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312233970021691555471/50000000000000000000)
  centralHi := (624467940043383110943/100000000000000000000)
  directionLo := (313233121279508719227/50000000000000000000)
  directionHi := (125293248511803487691/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree158.table
  base := (93909191099170711720973343856971420909731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-33424772697864864168391030047058800000000000)
      constant := (1362630082365648529457531973486331424020380214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree158.table
  base := (187818382198329593469977252232567901685127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3723338458983549178379348849758200000000000)
      constant := (152145184612943249210461474875897765755609191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313233121279508719227/50000000000000000000)
  centralHi := (125293248511803487691/20000000000000000000)
  directionLo := (628458191123324464147/100000000000000000000)
  directionHi := (157114547780831116037/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree159.table
  base := (191162531489881805856398512922715801635451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3737370796057372212319860556213200000000000)
      constant := (153357691770422790151930305140918421453969883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree159.table
  base := (191162531489871671299459438067506937713819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1248968529732425869058958306951900000000000)
      constant := (51369651454041384505134104579805820064852009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628458191123324464147/100000000000000000000)
  centralHi := (157114547780831116037/25000000000000000000)
  directionLo := (315221922982043068643/50000000000000000000)
  directionHi := (630443845964086137287/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree160.table
  base := (1519805556374028504409676065174967231743/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3942)
      previous := (1971)
      next := (1971)
      square := (19429389794524200840708516630000000000000)
      linear := (-3077081966469803241215132724070800000000000)
      constant := (127083775187901162101779991010972686752903808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree160.table
  base := (194535111215866966768560738619555805443709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3770472719411006035974400991953200000000000)
      constant := (156085356611316250457649355795093341579642397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315221922982043068643/50000000000000000000)
  centralHi := (630443845964086137287/100000000000000000000)
  directionLo := (79052908295447110479/12500000000000000000)
  directionHi := (632423266363576883833/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree161.table
  base := (98968060688282461470923107833339114990833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-34059466097819321395854174923638800000000000)
      constant := (1415736985765043410212759936978660234304554802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree161.table
  base := (7917444855062299437327624765260998970059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3794039849624734464771927063050700000000000)
      constant := (158074391360527526237047613395938155400298675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79052908295447110479/12500000000000000000)
  centralHi := (632423266363576883833/100000000000000000000)
  directionLo := (634396510679214774157/100000000000000000000)
  directionHi := (317198255339607387079/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree162.table
  base := (201365561972186190862803312790897102169649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1269297428313733597716366291944400000000000)
      constant := (53098726001046935241612771745372668123866139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree162.table
  base := (201365561972179820398665133526696153211759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-115685059995104936168771307095400000000000)
      constant := (4850789654841387526562803524891521153211759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634396510679214774157/100000000000000000000)
  centralHi := (317198255339607387079/50000000000000000000)
  directionLo := (159090909090909090909/25000000000000000000)
  directionHi := (636363636363636363637/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree163.table
  base := (12801464562685671934988069536764474080617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-34482595031122292880829604841358800000000000)
      constant := (1451707375856653002745786889167239180831091984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree163.table
  base := (102411716501482647142365626822513213635129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3841174110052191322366979205245700000000000)
      constant := (162090358359038670572175714642258053349918514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159090909090909090909/25000000000000000000)
  centralHi := (636363636363636363637/100000000000000000000)
  directionLo := (319162349992107371629/50000000000000000000)
  directionHi := (638324699984214743259/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree164.table
  base := (52077433617286195295343067533241462593359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-34694159497773778623317319800218800000000000)
      constant := (1469862307250267838730193163662254057560910492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree164.table
  base := (41661946893828021477615550096349646736129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3864741240265919751164505276343200000000000)
      constant := (164117290608353637417147937801294391711461285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319162349992107371629/50000000000000000000)
  centralHi := (638324699984214743259/100000000000000000000)
  directionLo := (320139878621019779727/50000000000000000000)
  directionHi := (128055951448407911891/20000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree165.table
  base := (211824466370929477598899708333431887345197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2158821088280466760078724070000000000000)
      linear := (-352583070347729943088939745041200000000000)
      constant := (15031620163729065199090621380948295662035591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree165.table
  base := (105912233185462737253996075580093925515619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (719607029426822253359574690000000000000)
      linear := (-117827526378171156968546404467900000000000)
      constant := (5035056222961151181814111339199969101031238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320139878621019779727/50000000000000000000)
  centralHi := (128055951448407911891/20000000000000000000)
  directionLo := (321114431495188509969/50000000000000000000)
  directionHi := (642228862990377019939/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree166.table
  base := (215367628708541189444707130733580805762313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-35117288431076750108292749717938800000000000)
      constant := (1506511642733446106407119712274674299311406961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree166.table
  base := (53841907177134440232327390899526695411159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3911875500693376608759557418538200000000000)
      constant := (168209052607138865374728482380457948794272988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321114431495188509969/50000000000000000000)
  centralHi := (642228862990377019939/100000000000000000000)
  directionLo := (80521508906578399209/12500000000000000000)
  directionHi := (644172071252627193673/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree167.table
  base := (43787844296438310077601773427811558424613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-35328852897728235850780464676798800000000000)
      constant := (1525006046823136649021394406296909764260550305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree167.table
  base := (43787844296437722815999969060403113361879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3935442630907105037557083489635700000000000)
      constant := (170273882356623250906859367659586144954710035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80521508906578399209/12500000000000000000)
  centralHi := (644172071252627193673/100000000000000000000)
  directionLo := (161527358809948809081/25000000000000000000)
  directionHi := (25844377409591809453/4000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree168.table
  base := (222539244692087606075987426196949246402369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3948935262708857954807575515073200000000000)
      constant := (171512623164256730567778755983196925131278177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree168.table
  base := (44507848938417018279898979846616748438397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (1606)
      previous := (803)
      next := (803)
      square := (7915677323695044786955321590000000000000)
      linear := (-1319669920373611155451536520244400000000000)
      constant := (57450448202059326163919860942900721164111835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell062.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161527358809948809081/25000000000000000000)
  centralHi := (25844377409591809453/4000000000000000000)
  directionLo := (81005125920936565773/12500000000000000000)
  directionHi := (129608201473498505237/20000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree169.table
  base := (5654192458460798449583545180752728307543/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (43362)
      previous := (21681)
      next := (21681)
      square := (213723287739766209247793682930000000000000)
      linear := (-35751981831031207335755894594518800000000000)
      constant := (1562334327699028051370948507729149612293610840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree169.table
  base := (113083849169214892234439857201917458603799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (4818)
      previous := (2409)
      next := (2409)
      square := (23747031971085134360865964770000000000000)
      linear := (-3982576891334561895152135631830700000000000)
      constant := (174441439355809733651604932525219283517850734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell062.Kernel169
