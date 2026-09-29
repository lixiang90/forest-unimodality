import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell178.Parameters
import ForestUnimodality.BinomialMassData.Q29_54.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_54.Batch050_099
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree000.table
  base := (72269688524697350697749699/2000000000000000000000000)
  polynomial :=
    { denominator := 6750000000000000000000000000000000000000
      center := (29)
      previous := (0)
      next := (25)
      square := (1286932960235367268131412282500000000000)
      linear := (-4802935768910974068113262105000000000000)
      constant := (243910198770853558604905234125000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree000.table
  base := (72269688524697350697749699/2000000000000000000000000)
  polynomial :=
    { denominator := 594000000000000000000000000000000000000000
      center := (2557)
      previous := (0)
      next := (2195)
      square := (113250100500712319595564280860000000000000)
      linear := (-422658347664165717993967065240000000000000)
      constant := (21464097491835113157231660603000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree001.table
  base := (22863961703942015451696179625844565237993/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 729000000000000000000000000000000000000000
      center := (3132)
      previous := (0)
      next := (2700)
      square := (138988759705419664958192526510000000000000)
      linear := (-668001286429687802459476132110000000000000)
      constant := (16986483935272711829588881102278188058496897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree001.table
  base := (22838347487569916806333466499918639312067/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-161727092628797393394940451646157500000000000)
      constant := (4106380433669862596814117033097058619531236006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (2492735499877659917/5000000000000000000)
  directionHi := (49854709997553198341/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree002.table
  base := (29588805231079706590249441591500932905089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-1634571019633980811125439913760000000000000)
      constant := (23005204739861620642908495352144180087809881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree002.table
  base := (73817714131659924819462668658941003486747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-989623280006687842728363424580175000000000000)
      constant := (13893009551973446052218447265624621140624932246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2492735499877659917/5000000000000000000)
  centralHi := (49854709997553198341/100000000000000000000)
  directionLo := (8813150878339658171/12500000000000000000)
  directionHi := (70505207026717265369/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree003.table
  base := (48931283965160829469643569447087418480747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1740)
      previous := (0)
      next := (1500)
      square := (77215977614122036087884736950000000000000)
      linear := (-536983185113496115925535434250000000000000)
      constant := (4628145684683485027051062560101580896940507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree003.table
  base := (12197396081343705166364714152094483016009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-130067899652154302053558287881062500000000000)
      constant := (1117644041031164023699852669097259771194233672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8813150878339658171/12500000000000000000)
  centralHi := (70505207026717265369/100000000000000000000)
  directionLo := (86350890712374197703/100000000000000000000)
  directionHi := (10793861339046774713/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree004.table
  base := (8249154041240483038215532171470504049881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-1394817445739494514711509508025000000000000)
      constant := (8208196239091416001647908022401997452363249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree004.table
  base := (6575738380473872873891981468788611465983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-270319782746417918847137151455790000000000000)
      constant := (1586083113097534117773417889227333007605788894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86350890712374197703/100000000000000000000)
  centralHi := (10793861339046774713/12500000000000000000)
  directionLo := (2492735499877659917/2500000000000000000)
  directionHi := (99709419995106396681/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree005.table
  base := (5638562878315548210612816368251498080249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-1581422724973622768590564288987500000000000)
      constant := (7104250882714327412471455425127217100501521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree005.table
  base := (22460188200808056227744300588178102340957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-1532586730594790469989346923628337500000000000)
      constant := (6868378589371333992192550374099968130661952026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2492735499877659917/2500000000000000000)
  centralHi := (99709419995106396681/100000000000000000000)
  directionLo := (3483703767283353923/3125000000000000000)
  directionHi := (111478520553067325537/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree006.table
  base := (1935360592786366949785283426346853110381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101250000000000000000000000000000000000000
      center := (435)
      previous := (0)
      next := (375)
      square := (19303994403530509021971184237500000000000)
      linear := (-196447556023083446941068785550000000000000)
      constant := (746098204039485539249675014880690203881722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree006.table
  base := (30818169210083316479818376925622532172911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-190397171939721260638112009997525000000000000)
      constant := (721977688815095461524443020975143625326700711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3483703767283353923/3125000000000000000)
  centralHi := (111478520553067325537/100000000000000000000)
  directionLo := (24423720153687304279/20000000000000000000)
  directionHi := (30529650192109130349/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree007.table
  base := (2631311431819447217780558533280230572173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-1954633283441879276348673850912500000000000)
      constant := (6810957619775143109127071057083163087114117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree007.table
  base := (523375174917798513000603478041763832333/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-378912472864038444299333851265422500000000000)
      constant := (1319353028399152062420503135388845926465092776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24423720153687304279/20000000000000000000)
  centralHi := (30529650192109130349/25000000000000000000)
  directionLo := (65951582169385663229/50000000000000000000)
  directionHi := (131903164338771326459/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree008.table
  base := (13854118880103284190994659927345555423953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-17129908501408060241821829055000000000000000)
      constant := (58040044872715698236430693140634909904061737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree008.table
  base := (3440835159498869257561412911905186042007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-2075550181182893097250330422676500000000000000)
      constant := (7032297016715651943227350270969953222317581852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65951582169385663229/50000000000000000000)
  centralHi := (131903164338771326459/100000000000000000000)
  directionLo := (141010414053434530737/100000000000000000000)
  directionHi := (70505207026717265369/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree009.table
  base := (8457858341887953368727459250585129389771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (51477318409414690725256491300000000000000)
      linear := (-689731508714114306402009900100000000000000)
      constant := (2359497112284811808011447328490798493523817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree009.table
  base := (8385915357664987073882793759536289414951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-83575481409096073074221910704662500000000000)
      constant := (286054988775393600460590034079686698143644917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141010414053434530737/100000000000000000000)
  centralHi := (70505207026717265369/50000000000000000000)
  directionLo := (7478206499632979751/5000000000000000000)
  directionHi := (149564129992659595021/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree010.table
  base := (858366713430777045900061730334497919207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-4023118593830822460777341110080000000000000)
      constant := (14214270526456980255831919632713848983101903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree010.table
  base := (1058573184501996205068200828837982778247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-2437525814908294848757652755375275000000000000)
      constant := (8620186798267685457091326038699558179045558492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7478206499632979751/5000000000000000000)
  centralHi := (149564129992659595021/100000000000000000000)
  directionLo := (157654435679435636539/100000000000000000000)
  directionHi := (7882721783971781827/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree011.table
  base := (124378007267645262977027248463991947041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-2701054400378392291864892974762500000000000)
      constant := (9983956591454208205489868526177125129392889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree011.table
  base := (237150978749904462777635378391964132183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (345195)
      previous := (0)
      next := (296325)
      square := (15288763567596163145401177916100000000000000)
      linear := (-238046693797363247682846720156787500000000000)
      constant := (880969058916823497293387058006591657128901908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157654435679435636539/100000000000000000000)
  centralHi := (7882721783971781827/5000000000000000000)
  directionLo := (165349367093864133369/100000000000000000000)
  directionHi := (16534936709386413337/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree012.table
  base := (-333347296299621168003716252797779573511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (696)
      previous := (0)
      next := (600)
      square := (30886391045648814435153894780000000000000)
      linear := (-513361720820003652576701823240000000000000)
      constant := (1998591446659968893850719350083379854545609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree012.table
  base := (-213057226949981790674427682390799694499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-311055716514855177807219454230450000000000000)
      constant := (1212702610590384775867032831763120927553722408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165349367093864133369/100000000000000000000)
  centralHi := (16534936709386413337/10000000000000000000)
  directionLo := (172701781424748395407/100000000000000000000)
  directionHi := (10793861339046774713/6250000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree013.table
  base := (-962297941925425898971461232237902159053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-6148529917693297599246005073375000000000000)
      constant := (25288175641890264939177516449942319326050363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree013.table
  base := (-1940008114796553825638618160221092481479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-2980489265496397476018636254423437500000000000)
      constant := (12277495026813120752648725599427697728477437778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172701781424748395407/100000000000000000000)
  centralHi := (10793861339046774713/6250000000000000000)
  directionLo := (89876856609782616403/50000000000000000000)
  directionHi := (179753713219565232807/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree014.table
  base := (-1131718110510131467215907537750435239149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-5217392380929243285603291708240000000000000)
      constant := (22688491958990795232919946618919932710660379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree014.table
  base := (-177621216899080107116421550360830025687/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-3161477082359098351772297420772825000000000000)
      constant := (13770841058779192507206827530541531603953613344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89876856609782616403/50000000000000000000)
  centralHi := (179753713219565232807/100000000000000000000)
  directionLo := (18653924392781758983/10000000000000000000)
  directionHi := (186539243927817589831/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree015.table
  base := (-7169209680867428021621269432559846205157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-3064422682057693606560988532100000000000000)
      constant := (14083526551333530600707402114337652457382283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree015.table
  base := (-719000855818843632872931701735257406631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (84381)
      previous := (0)
      next := (72435)
      square := (3737253316523506546653621268380000000000000)
      linear := (-74276997760484427278354635269382500000000000)
      constant := (341951942742876413473326524657313218690219138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18653924392781758983/10000000000000000000)
  centralHi := (186539243927817589831/100000000000000000000)
  directionLo := (193086461550523946579/100000000000000000000)
  directionHi := (9654323077526197329/5000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree016.table
  base := (-2108538109201857958010585120752512786291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-7268161593098067122520333759150000000000000)
      constant := (35260456943638789771783101416971418178793861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree016.table
  base := (-8451281870605079665195707864002207652211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-3523452716084500103279619753471600000000000000)
      constant := (17123819912104273462725529215070729265206119901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193086461550523946579/100000000000000000000)
  centralHi := (9654323077526197329/5000000000000000000)
  directionLo := (2492735499877659917/1250000000000000000)
  directionHi := (199418839990212793361/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree017.table
  base := (-2373034666385856291045231509796429659857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-7641372151566323630278443321075000000000000)
      constant := (39071124866370796948400515822752152777964247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree017.table
  base := (-9506252274834541543874386159978229654039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-3704440532947200979033280919820987500000000000)
      constant := (18975387768224126707036047941952178387321873849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2492735499877659917/1250000000000000000)
  centralHi := (199418839990212793361/100000000000000000000)
  directionLo := (205556235254448615901/100000000000000000000)
  directionHi := (102778117627224307951/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree018.table
  base := (-1037187316098332368348620407034297454281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (116)
      previous := (0)
      next := (100)
      square := (5147731840941469072525649130000000000000)
      linear := (-118734558667178965007948931600000000000000)
      constant := (638736400888988855576530152440073968734413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree018.table
  base := (-5191749656935934433034384266365660417541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-143904753696663031658775632821125000000000000)
      constant := (775556296995590675819043581960468337331787106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205556235254448615901/100000000000000000000)
  centralHi := (102778117627224307951/50000000000000000000)
  directionLo := (105757810540075898053/50000000000000000000)
  directionHi := (211515621080151796107/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree019.table
  base := (-5547463163767272968330727158267673056691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-16775586537005673291589324889850000000000000)
      constant := (94774544636686780301384474170410366341672261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree019.table
  base := (-11104496787952000110992211639922898877251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-4066416166672602730540603252519762500000000000)
      constant := (23015822481629814394646984550596473434811566541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105757810540075898053/50000000000000000000)
  centralHi := (211515621080151796107/100000000000000000000)
  directionLo := (217311642738861291981/100000000000000000000)
  directionHi := (108655821369430645991/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree020.table
  base := (-11677682711279665216480111436440724826259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-35044015307884372614211088027400000000000000)
      constant := (207543338231428700654487650970834711601657189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree020.table
  base := (-11685553010242620093191952256042791164763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-4247403983535303606294264418869150000000000000)
      constant := (25201356616474516839828074246302690184147420533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217311642738861291981/100000000000000000000)
  centralHi := (108655821369430645991/50000000000000000000)
  directionLo := (222957041106134651073/100000000000000000000)
  directionHi := (111478520553067325537/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree021.table
  base := (-12132692248829035405909324969499866266293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-4059650837973044293915947363900000000000000)
      constant := (25159158467822607020015133003845510832430267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree021.table
  base := (-3034789147974730797318171337165550471603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-492043533377556053560880620579837500000000000)
      constant := (3055057868390407449099058029072978556186275988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222957041106134651073/100000000000000000000)
  centralHi := (111478520553067325537/50000000000000000000)
  directionLo := (114231491156929606259/50000000000000000000)
  directionHi := (228462982313859212519/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree022.table
  base := (-12469629317941292706865813661144488245589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-38029699775630424676275964522800000000000000)
      constant := (246209300588911802388517298566725668068965619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree022.table
  base := (-3118732960144527239967195838354868011137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (345195)
      previous := (0)
      next := (296325)
      square := (15288763567596163145401177916100000000000000)
      linear := (-419034510660064123436507886506175000000000000)
      constant := (2717951466199375553163030112589418316174769588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114231491156929606259/50000000000000000000)
  centralHi := (228462982313859212519/100000000000000000000)
  directionLo := (116919658736975107291/50000000000000000000)
  directionHi := (233839317473950214583/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree023.table
  base := (-3173996908062792424084804342470358415899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-9880635502375862676827100692625000000000000)
      constant := (66717124612428499557751377027582858714809629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree023.table
  base := (-1270033115722120717153377907759262968607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-958073486824681246711049583583462500000000000)
      constant := (6481307037135660334771116120277177204979290274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116919658736975107291/50000000000000000000)
  centralHi := (233839317473950214583/100000000000000000000)
  directionLo := (119547394895939711763/50000000000000000000)
  directionHi := (239094789791879423527/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree024.table
  base := (-12817592702479646700294569083149510225737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-4557264915930719637593426779800000000000000)
      constant := (32045085888388272894441368513064889671715303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree024.table
  base := (-12821145732964432726509565435804218733943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-552372805665123012145434342696300000000000000)
      constant := (3891357461421138269862935024250857852188624657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119547394895939711763/50000000000000000000)
  centralHi := (239094789791879423527/100000000000000000000)
  directionLo := (244237201536873042791/100000000000000000000)
  directionHi := (30529650192109130349/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree025.table
  base := (-3209746325019191593079797098313136276517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-10627056619312375692343319816475000000000000)
      constant := (77704453500966523687738142026423473654419107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree025.table
  base := (-6420943859323940890745628297858063226459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-5152343067848807985062570250616087500000000000)
      constant := (37744114017215505307639915763483817998589556138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244237201536873042791/100000000000000000000)
  centralHi := (30529650192109130349/12500000000000000000)
  directionLo := (249273549987765991701/100000000000000000000)
  directionHi := (124636774993882995851/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree026.table
  base := (-797731984977958496724683219219385348243/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-5500133588890316100050714689200000000000000)
      constant := (41762754524612751232437336174940636162261706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree026.table
  base := (-12766079540517727776435195980990558943307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-5333330884711508860816231416965475000000000000)
      constant := (40571915069257335597510973140006358473669832837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249273549987765991701/100000000000000000000)
  centralHi := (124636774993882995851/50000000000000000000)
  directionLo := (1986016711890883253/781250000000000000)
  directionHi := (50842027824406611277/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree027.table
  base := (-6297272883620206542187029049064532462699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (580)
      previous := (0)
      next := (500)
      square := (25738659204707345362628245650000000000000)
      linear := (-842479832314732496878484365950000000000000)
      constant := (6634378102916156265606384874037757623507127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree027.table
  base := (-12596474909426664353313682538192189870493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-204234025984229990243329354937587500000000000)
      constant := (1611310274327227038700550104816585881318099369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1986016711890883253/781250000000000000)
  centralHi := (50842027824406611277/20000000000000000000)
  directionLo := (25905267213712259311/10000000000000000000)
  directionHi := (259052672137122593111/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree028.table
  base := (-6166829497909854633608569331402922437171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-23493376589434290431235297004500000000000000)
      constant := (191639687467993417264223096804207269543302341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree028.table
  base := (-1541903602952638933368078943408275646561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-5695306518436910612323553749664250000000000000)
      constant := (46544310939708570192057021344679514057940006008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25905267213712259311/10000000000000000000)
  centralHi := (259052672137122593111/100000000000000000000)
  directionLo := (263806328677542652917/100000000000000000000)
  directionHi := (131903164338771326459/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree029.table
  base := (-5991376542022479310686598108660663292351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-24239797706370803446751516128350000000000000)
      constant := (204584833918931126119648191426073876459876121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree029.table
  base := (-2396805804639070356195780123636187127603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-1175258867059922297615442983202727500000000000)
      constant := (9937713358802335891891900036996749554036266973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263806328677542652917/100000000000000000000)
  centralHi := (131903164338771326459/50000000000000000000)
  directionLo := (268475829748720199283/100000000000000000000)
  directionHi := (67118957437180049821/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree030.table
  base := (-11543162122363613373678985312591294100257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-5552493071846070324948385611600000000000000)
      constant := (48436258190129166533547928540180105177879183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree030.table
  base := (-11544198035905351775165734808144671672807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-673031350240256929314541786929225000000000000)
      constant := (5882003145654847977767787577078803760434818593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268475829748720199283/100000000000000000000)
  centralHi := (67118957437180049821/25000000000000000000)
  directionLo := (136532746317691058127/50000000000000000000)
  directionHi := (54613098527076423251/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree031.table
  base := (-2753983118094729254711867639345591499083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-12866319970121914738891977188025000000000000)
      constant := (115887144939569702427176341109260813797168493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree031.table
  base := (-5508386312039994612660870430560280631933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-6238269969025013239584537248712412500000000000)
      constant := (56292604038586159233681778306577726958350644006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136532746317691058127/50000000000000000000)
  centralHi := (54613098527076423251/20000000000000000000)
  directionLo := (4337176213181286049/1562500000000000000)
  directionHi := (277579277643602307137/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree032.table
  base := (-10401885068408076401051373841511762874949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-52958122114360684986600346999800000000000000)
      constant := (492035837518093941170216491320737924864162179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree032.table
  base := (-2600641442515993873559806438026726188673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-6419257785887714115338198415061800000000000000)
      constant := (59752222264729617116174023917631602038493373372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4337176213181286049/1562500000000000000)
  centralHi := (277579277643602307137/100000000000000000000)
  directionLo := (141010414053434530737/50000000000000000000)
  directionHi := (11280833124274762459/4000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree033.table
  base := (-9701664123885797996794351554352792207809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-6050107149803745668625865027500000000000000)
      constant := (57931958595445999129454841333872423831167471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree033.table
  base := (-9702215114200933924011612392273858345461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (38355)
      previous := (0)
      next := (32925)
      square := (1698751507510684793933464212900000000000000)
      linear := (-66669147502529444354463228095062500000000000)
      constant := (639563906502090250262667740255550007839194249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141010414053434530737/50000000000000000000)
  centralHi := (11280833124274762459/4000000000000000000)
  directionLo := (28639350480593011739/10000000000000000000)
  directionHi := (286393504805930117391/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree034.table
  base := (-891577525406842511652503214805110088349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 729000000000000000000000000000000000000000
      center := (3132)
      previous := (0)
      next := (2700)
      square := (138988759705419664958192526510000000000000)
      linear := (-5594380658210673704866522349520000000000000)
      constant := (55160358068751708842001955634777074745593579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree034.table
  base := (-8916220849916676398902080592246560231261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-6781233419613115866845520747760575000000000000)
      constant := (66986373353956214772673054581665840356060698451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28639350480593011739/10000000000000000000)
  centralHi := (286393504805930117391/100000000000000000000)
  directionLo := (290700415727195767063/100000000000000000000)
  directionHi := (36337551965899470883/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree035.table
  base := (-2011153835121706901153419513734076860839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-14359162203994940769924415435725000000000000)
      constant := (145670852044241806454612130759081607968448369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree035.table
  base := (-8044975395607893340169903163753736877739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-6962221236475816742599181914109962500000000000)
      constant := (70760827480643103440812009611280991545626520549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290700415727195767063/100000000000000000000)
  centralHi := (36337551965899470883/12500000000000000000)
  directionLo := (7373611047720469627/2500000000000000000)
  directionHi := (294944441908818785081/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree036.table
  base := (-1772123985188243364563530781423337841823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (290)
      previous := (0)
      next := (250)
      square := (12869329602353672681314122825000000000000)
      linear := (-545643435646785084358612036950000000000000)
      constant := (5690989654646900737874316362901569878270779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree036.table
  base := (-7088786642021385904316498376954757850917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-264563298271796948827883077054050000000000000)
      constant := (2764450443149359859155819917405645056101054161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7373611047720469627/2500000000000000000)
  centralHi := (294944441908818785081/100000000000000000000)
  directionLo := (299128259985319190041/100000000000000000000)
  directionHi := (149564129992659595021/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree037.table
  base := (-377978852947708796003077108424946549981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-7552791660465726892720317279787500000000000)
      constant := (80929228244303389691403874903988302930127702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree037.table
  base := (-6047896174288021053784256555341083146483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-7324196870201218494106504246808737500000000000)
      constant := (78624355497142244397968358249635257068606881053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299128259985319190041/100000000000000000000)
  centralHi := (149564129992659595021/50000000000000000000)
  directionLo := (9476698810375020083/3125000000000000000)
  directionHi := (303254361932000642657/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree038.table
  base := (-4922304488806369258386857524127387997503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-61915175517598841172794976486000000000000000)
      constant := (681104097945447266711800278221011134149820313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree038.table
  base := (-4922493559574862450105827317959783222097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-7505184687063919369860165413158125000000000000)
      constant := (82713391355441448524575537560082990169262045727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9476698810375020083/3125000000000000000)
  centralHi := (303254361932000642657/100000000000000000000)
  directionLo := (307325072422874361509/100000000000000000000)
  directionHi := (30732507242287436151/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree039.table
  base := (-3712575232583385598648892989418943171711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-7045335305719096355980823859300000000000000)
      constant := (79515287640650517795570955573032065603091409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree039.table
  base := (-3712727552489030534942188571164487921769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-854019167102957805068202953278612500000000000)
      constant := (9656361824270576565554466944572674275753742031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307325072422874361509/100000000000000000000)
  centralHi := (30732507242287436151/10000000000000000000)
  directionLo := (311342564145452335549/100000000000000000000)
  directionHi := (6226851282909046711/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree040.table
  base := (-1209296126218645765612797903580462818719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-32450429992672446617429926490700000000000000)
      constant := (375517106060522461241357734326289842605153849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree040.table
  base := (-2418714884670197014179880045239019514637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-7867160320789321121367487745856900000000000000)
      constant := (91205940389342262292707807289779886327633384867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311342564145452335549/100000000000000000000)
  centralHi := (6226851282909046711/2000000000000000000)
  directionLo := (157654435679435636539/50000000000000000000)
  directionHi := (315308871358871273079/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree041.table
  base := (-1040448490962526971796938693257961961551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-66393702219217919265892291229100000000000000)
      constant := (787293900255866706981000183596989945730029321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree041.table
  base := (-130068395033121095415676217452387220797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-8048148137652021997121148912206287500000000000)
      constant := (95609435187852500086846798361838218302000739416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157654435679435636539/50000000000000000000)
  centralHi := (315308871358871273079/100000000000000000000)
  directionLo := (159612950967759320363/50000000000000000000)
  directionHi := (319225901935518640727/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree042.table
  base := (210891537899231620972136442083235839279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1740)
      previous := (0)
      next := (1500)
      square := (77215977614122036087884736950000000000000)
      linear := (-3771474691838385849829151637600000000000000)
      constant := (45800922220599170631573038322458742102981599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree042.table
  base := (210851867026277464107310790105980926269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-914348439390524763652756675395075000000000000)
      constant := (11124192719212696316465323207822949625616724938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159612950967759320363/50000000000000000000)
  centralHi := (319225901935518640727/100000000000000000000)
  directionLo := (323095448088464246437/100000000000000000000)
  directionHi := (161547724044232123219/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree043.table
  base := (1968045148252212201263130142822880564211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-69379386686963971327957167724500000000000000)
      constant := (862402269494396378268191238772092879931309819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree043.table
  base := (1967981384231539449029916388108376202841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-8410123771377423748628471244905062500000000000)
      constant := (104730833268300552506493247881001077928351401769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323095448088464246437/100000000000000000000)
  centralHi := (161547724044232123219/50000000000000000000)
  directionLo := (326919195955859443477/100000000000000000000)
  directionHi := (163459597977929721739/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree044.table
  base := (3598292735170728089323766295016501675021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-70872228920836997358989605972200000000000000)
      constant := (901250876028095421646156483612267029721090309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree044.table
  base := (3598241518060957671550719729025072699827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (345195)
      previous := (0)
      next := (296325)
      square := (15288763567596163145401177916100000000000000)
      linear := (-781010144385465874943830219204950000000000000)
      constant := (9949884333527626779078819534435658307979912713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326919195955859443477/100000000000000000000)
  centralHi := (163459597977929721739/50000000000000000000)
  directionLo := (330698734187728266739/100000000000000000000)
  directionHi := (16534936709386413337/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree045.table
  base := (265624525468714376389984106227202547651/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (58)
      previous := (0)
      next := (50)
      square := (2573865920470734536262824565000000000000)
      linear := (-134009391027240784055596378185000000000000)
      constant := (1742522951515496635480389641474384468786577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree045.table
  base := (5312449391530426051914600096835729742191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-324892570559363907412436799170512500000000000)
      constant := (4232274615173699300603283283076153344692737997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330698734187728266739/100000000000000000000)
  centralHi := (16534936709386413337/5000000000000000000)
  directionLo := (33443556165920197661/10000000000000000000)
  directionHi := (334435561659201976611/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree046.table
  base := (7110610731596416754222869188017581241973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-73857913388583049421054482467600000000000000)
      constant := (981536802643289403435113828968564816725398317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree046.table
  base := (1777644434469133414724449359188669581947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-8953087221965526375889454743953225000000000000)
      constant := (119198891685784578430925832523120185608115851692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33443556165920197661/10000000000000000000)
  centralHi := (334435561659201976611/100000000000000000000)
  directionLo := (67626218883284024097/20000000000000000000)
  directionHi := (169065547208210060243/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree047.table
  base := (8992631620415174207915315913050392260649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-75350755622456075452086920715300000000000000)
      constant := (1022974086624202487075532480893188735958013121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree047.table
  base := (1124075644768182128023605832717368684341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-9134075038828227251643115910302612500000000000)
      constant := (124231157009507668699462280495121404041091282152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67626218883284024097/20000000000000000000)
  centralHi := (169065547208210060243/50000000000000000000)
  directionLo := (34178667194638551149/10000000000000000000)
  directionHi := (341786671946385511491/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree048.table
  base := (1095853607239367088331201330622274134847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 81000000000000000000000000000000000000000
      center := (348)
      previous := (0)
      next := (300)
      square := (15443195522824407217576947390000000000000)
      linear := (-853817753959212238701326210700000000000000)
      constant := (11836380369918910466617883006820404204922607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree048.table
  base := (5479257429103994851678567629430182396633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1035006983965658680821864119628000000000000000)
      constant := (14374245455496200972293468073322990435338800066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34178667194638551149/10000000000000000000)
  centralHi := (341786671946385511491/100000000000000000000)
  directionLo := (172701781424748395407/50000000000000000000)
  directionHi := (69080712569899358163/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree049.table
  base := (6504155328589715744946054952935208443019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-39168220045101063757075898605350000000000000)
      constant := (554218616429030406854277548707477266954960851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree049.table
  base := (13008293657638740792473132286126558945407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-9496050672553629003150438243001387500000000000)
      constant := (134610046793026855278217909022614510684890406063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172701781424748395407/50000000000000000000)
  centralHi := (69080712569899358163/20000000000000000000)
  directionLo := (348982969982872388381/100000000000000000000)
  directionHi := (174491484991436194191/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree050.table
  base := (3028388965697151694208869894862766853863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-15965856464815030709036847091680000000000000)
      constant := (230492615526407219939119951099854957036466127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree050.table
  base := (757096560596678927651005403158255652593/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-1935407697883265975780819881870155000000000000)
      constant := (27991333835542488665133909474973644728938303748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348982969982872388381/100000000000000000000)
  centralHi := (174491484991436194191/50000000000000000000)
  directionLo := (352526035133586326843/100000000000000000000)
  directionHi := (88131508783396581711/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree051.table
  base := (3471886060914758888235779184155363523697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (696)
      previous := (0)
      next := (600)
      square := (30886391045648814435153894780000000000000)
      linear := (-1807158323509959546138148304580000000000000)
      constant := (26607816923938670509392187874591584445419457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree051.table
  base := (8679709701070493681969488977066518049729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1095336256253225639406417841744462500000000000)
      constant := (16156452837484219850175347435558330933685787858) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352526035133586326843/100000000000000000000)
  centralHi := (88131508783396581711/25000000000000000000)
  directionLo := (356033843273285850291/100000000000000000000)
  directionHi := (89008460818321462573/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree052.table
  base := (9830380290910103520503993309850851352207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-41407483395910602803624555976900000000000000)
      constant := (621551639976265812049890207516481270635758903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree052.table
  base := (19660751855870264058294581096581079460989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-10039014123141731630411421742049550000000000000)
      constant := (150964265309861249720291464053568989188174378701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356033843273285850291/100000000000000000000)
  centralHi := (89008460818321462573/25000000000000000000)
  directionLo := (89876856609782616403/25000000000000000000)
  directionHi := (359507426439130465613/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree053.table
  base := (4409186110555909116908192588700978126349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-16861561805138846327656310040300000000000000)
      constant := (257943525806916543935381689477758013054108421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree053.table
  base := (22045923571397492827825329212578913886523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-10220001940004432506165082908398937500000000000)
      constant := (156625238054025191642278612335092299586891307307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89876856609782616403/25000000000000000000)
  centralHi := (359507426439130465613/100000000000000000000)
  directionLo := (181473883640199681047/50000000000000000000)
  directionHi := (72589553456079872419/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree054.table
  base := (12257468103146507155303248261760815459563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (580)
      previous := (0)
      next := (500)
      square := (25738659204707345362628245650000000000000)
      linear := (-1588900949251245512394703489800000000000000)
      constant := (24762866775912198102669234315617542017408201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree054.table
  base := (12257465311338895238109940097020559419497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-385221842846930865996990521286975000000000000)
      constant := (6014481237908789307988005355132696397746993398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181473883640199681047/50000000000000000000)
  centralHi := (72589553456079872419/20000000000000000000)
  directionLo := (366355802305309564187/100000000000000000000)
  directionHi := (91588950576327391047/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree055.table
  base := (5413554878403632846916675859244962230007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-17458698698688056740069285339380000000000000)
      constant := (277106961649991982478336434263664577465675103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree055.table
  base := (13533884963924615360366890084739532976913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (345195)
      previous := (0)
      next := (296325)
      square := (15288763567596163145401177916100000000000000)
      linear := (-961997961248166750697491385554337500000000000)
      constant := (15296502831504513644091768662044578020508730694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366355802305309564187/100000000000000000000)
  centralHi := (91588950576327391047/25000000000000000000)
  directionLo := (184866212429223525899/50000000000000000000)
  directionHi := (369732424858447051799/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree056.table
  base := (29704442635540535729313335449280074460907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-88786335727313309731378864944600000000000000)
      constant := (1434737634282838223151340619146525174282001203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree056.table
  base := (29704439067562394039102797414076830246531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-10762965390592535133426066407447100000000000000)
      constant := (174236851009653815003639138800600678119216252979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184866212429223525899/50000000000000000000)
  centralHi := (369732424858447051799/100000000000000000000)
  directionLo := (373078487855635179661/100000000000000000000)
  directionHi := (186539243927817589831/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree057.table
  base := (32424938993201280566478899579341666076879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-10031019773465148418045700354700000000000000)
      constant := (164978142508996258829407840472101674952227199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree057.table
  base := (32424936142411084062943597677283856140099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1215994800828359556575525285977387500000000000)
      constant := (20035216982811676099567385512445216495904110299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373078487855635179661/100000000000000000000)
  centralHi := (186539243927817589831/50000000000000000000)
  directionLo := (37639480629996405021/10000000000000000000)
  directionHi := (376394806299964050211/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree058.table
  base := (35229261938109069581743819716963593066879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-91772020195059361793443741440000000000000000)
      constant := (1535731752031240452370870878939766459345754791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree058.table
  base := (17614629830524069149610630277941307857753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-11124941024317936884933388740145875000000000000)
      constant := (186501836521953217906063330422861754337149068754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37639480629996405021/10000000000000000000)
  centralHi := (376394806299964050211/100000000000000000000)
  directionLo := (94920539900002540193/25000000000000000000)
  directionHi := (379682159600010160773/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree059.table
  base := (19058705135318694223584137129900924216439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-46632431214466193912238089843850000000000000)
      constant := (793761520879566431462436716635485273753784031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree059.table
  base := (38117408452381759035442578306990418866749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-11305928841180637760687049906495262500000000000)
      constant := (192791501936297377649088407871373156529692062541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94920539900002540193/25000000000000000000)
  centralHi := (379682159600010160773/100000000000000000000)
  directionLo := (382941293708928338541/100000000000000000000)
  directionHi := (191470646854464169271/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree060.table
  base := (41089383048147383048655724586434548875169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-10528633851422823761723179770600000000000000)
      constant := (182241905675273315164166872287501198458888689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree060.table
  base := (41089381596669365131094558308315470071709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1276324073115926515160079008093850000000000000)
      constant := (22131772111911998976150910154591268672172819909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382941293708928338541/100000000000000000000)
  centralHi := (191470646854464169271/50000000000000000000)
  directionLo := (386172923101047893159/100000000000000000000)
  directionHi := (9654323077526197329/2500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree061.table
  base := (882903590596126575951142035838318420651/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 729000000000000000000000000000000000000000
      center := (3132)
      previous := (0)
      next := (2700)
      square := (138988759705419664958192526510000000000000)
      linear := (-9625054689667843988654105618310000000000000)
      constant := (169369407944615431680363095965768170643272895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree061.table
  base := (11036294592860388095044444310300309144217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-11667904474906039512194372239194037500000000000)
      constant := (205685177670956753639265677851191164799083949412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386172923101047893159/100000000000000000000)
  centralHi := (9654323077526197329/2500000000000000000)
  directionLo := (389377732600810110019/100000000000000000000)
  directionHi := (19468886630040505501/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree062.table
  base := (23642399566629490063786030201071048404663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-48871694565275732958786747215400000000000000)
      constant := (874036913220339664942713904315430794286999327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree062.table
  base := (47284798209064214529455567747341782465919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-11848892291768740387948033405543425000000000000)
      constant := (212289187877473229332319114059973588477036249071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389377732600810110019/100000000000000000000)
  centralHi := (19468886630040505501/5000000000000000000)
  directionLo := (15702255163092369577/4000000000000000000)
  directionHi := (196278189538654619713/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree063.table
  base := (5050824140060565318886694451852986795159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (116)
      previous := (0)
      next := (100)
      square := (5147731840941469072525649130000000000000)
      linear := (-367541597646016636846688639550000000000000)
      constant := (6678949598989725948875420971692530643469293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree063.table
  base := (1578382520732309536551018496885012666463/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-445551115134497824581544243403437500000000000)
      constant := (8111036281015076998525961761278422154827707872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15702255163092369577/4000000000000000000)
  centralHi := (196278189538654619713/50000000000000000000)
  directionLo := (24731843313519623711/6250000000000000000)
  directionHi := (395709493016313979377/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree064.table
  base := (13453876492921962238956873637830309277909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-25182268399574379494909592731550000000000000)
      constant := (464855443760809699986691431398778295463595661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree064.table
  base := (53815505383840672771874105647087318939739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-12210867925494142139455355738242200000000000000)
      constant := (225811552769822528408504254396647125316355437451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24731843313519623711/6250000000000000000)
  centralHi := (395709493016313979377/100000000000000000000)
  directionLo := (398837679980425586721/100000000000000000000)
  directionHi := (199418839990212793361/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree065.table
  base := (28603296281555841146384065741560513151387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-51110957916085272005335404586950000000000000)
      constant := (958194988091061784436359605620785114087361123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree065.table
  base := (57206592094455706507696100522177273005751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-12391855742356843015209016904591587500000000000)
      constant := (232729907400388994102859228683632545621439289959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398837679980425586721/100000000000000000000)
  centralHi := (199418839990212793361/50000000000000000000)
  directionLo := (401941521966950440699/100000000000000000000)
  directionHi := (4019415219669504407/1000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree066.table
  base := (30340750475888292788342813783170370134511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1740)
      previous := (0)
      next := (1500)
      square := (77215977614122036087884736950000000000000)
      linear := (-5761931003669087224539069301200000000000000)
      constant := (109678944165624444398725264792686799980895391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree066.table
  base := (1213630011564663345346158540632033248761/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1782000000000000000000000000000000000000000
      center := (7671)
      previous := (0)
      next := (6585)
      square := (339750301502136958786692842580000000000000)
      linear := (-25399683958019280587803390042305000000000000)
      constant := (484349582747396120446930034372239228746460510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401941521966950440699/100000000000000000000)
  centralHi := (4019415219669504407/1000000000000000000)
  directionLo := (405021578672110548689/100000000000000000000)
  directionHi := (40502157867211054869/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree067.table
  base := (32120115480970760758102728540757952306057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-52603800149958298036367842834650000000000000)
      constant := (1016457415656236437337180180713000047231115553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree067.table
  base := (64240230664276148128232042070947178666697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-12753831376082244766716339237290362500000000000)
      constant := (246880960933464139700892847788827549604885675673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405021578672110548689/100000000000000000000)
  centralHi := (40502157867211054869/10000000000000000000)
  directionLo := (408078388669369215493/100000000000000000000)
  directionHi := (204039194334684607747/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree068.table
  base := (3394139122753441483119387074462145829267/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 364500000000000000000000000000000000000000
      center := (1566)
      previous := (0)
      next := (1350)
      square := (69494379852709832479096263255000000000000)
      linear := (-5335022126689481105188406195850000000000000)
      constant := (104623574253741412044867941262962904309535643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree068.table
  base := (2121336944310037310428374343406855158443/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-12934819192944945642470000403639750000000000000)
      constant := (254113659809019645625923987004504727923475154784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408078388669369215493/100000000000000000000)
  centralHi := (204039194334684607747/50000000000000000000)
  directionLo := (411112470508897231803/100000000000000000000)
  directionHi := (102778117627224307951/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree069.table
  base := (8951144415231132851345580696913935642671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101250000000000000000000000000000000000000
      center := (435)
      previous := (0)
      next := (375)
      square := (19303994403530509021971184237500000000000)
      linear := (-1502684510661981224094452252287500000000000)
      constant := (29901263280397493206027682026346903787056351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree069.table
  base := (8951144391619535270838379751702691215877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1457311889978627390913740174443237500000000000)
      constant := (29050126675250971233568800009231583909729483816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411112470508897231803/100000000000000000000)
  centralHi := (102778117627224307951/25000000000000000000)
  directionLo := (207062161872267857239/50000000000000000000)
  directionHi := (414124323744535714479/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree070.table
  base := (75419349475938336398262218990541229001791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-109686127001535674165833000412400000000000000)
      constant := (2214173244590901992637782293534604555942305639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree070.table
  base := (75419349325513100209844658821256442402741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-13296794826670347393977322736338525000000000000)
      constant := (268893401730783486141811612342990764215403380869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207062161872267857239/50000000000000000000)
  centralHi := (414124323744535714479/100000000000000000000)
  directionLo := (417114429894015004209/100000000000000000000)
  directionHi := (41711442989401500421/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree071.table
  base := (39656682424520174311410795893745885607783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-55589484617704350098432719330050000000000000)
      constant := (1138159175115943841147512735990228250608073807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree071.table
  base := (79313364729273281602133097694603674270467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-13477782643533048269730983902687912500000000000)
      constant := (276440444763744003957843955898663137300598623603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417114429894015004209/100000000000000000000)
  centralHi := (41711442989401500421/10000000000000000000)
  directionLo := (84016650667531204227/20000000000000000000)
  directionHi := (26255203333603501321/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree072.table
  base := (83291201387044245754691057217719174096739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (51477318409414690725256491300000000000000)
      linear := (-4173030054417841712144365811400000000000000)
      constant := (86641713817486287682841986926478417700611953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree072.table
  base := (83291201291705820140616121698103471082183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-505880387422064783166097965519900000000000000)
      constant := (10521935895240984704594802385151429040025491861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84016650667531204227/20000000000000000000)
  centralHi := (26255203333603501321/6250000000000000000)
  directionLo := (105757810540075898053/25000000000000000000)
  directionHi := (423031242160303592213/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree073.table
  base := (87352859046991549846716234213451033543803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-114164653703154752258930315155500000000000000)
      constant := (2403197013080311517639431274839580803453432387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree073.table
  base := (87352858971113744005906418955330241072801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-13839758277258450021238306235386687500000000000)
      constant := (291848874950393187153242402450959479531665703409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105757810540075898053/25000000000000000000)
  centralHi := (423031242160303592213/100000000000000000000)
  directionLo := (13311213404400434117/3125000000000000000)
  directionHi := (85191765788162778349/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree074.table
  base := (45749168897347040540529945048155289894289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-57828747968513889144981376701600000000000000)
      constant := (1233965285115754874907957506415955206332936681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree074.table
  base := (1143729221678948693145576003139777836203/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-2804149218824230179398393480347215000000000000)
      constant := (59942052419495385520348737048064182547958086832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13311213404400434117/3125000000000000000)
  centralHi := (85191765788162778349/20000000000000000000)
  directionLo := (428866431493034531601/100000000000000000000)
  directionHi := (214433215746517265801/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree075.table
  base := (19145527520572611464033382271937150096419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (696)
      previous := (0)
      next := (600)
      square := (30886391045648814435153894780000000000000)
      linear := (-2603340848242240096022115370020000000000000)
      constant := (56300598766796243150842381849901909157809939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree075.table
  base := (598297734717669653682671430513498670633/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (84381)
      previous := (0)
      next := (72435)
      square := (3737253316523506546653621268380000000000000)
      linear := (-315594086910752261616569523735232500000000000)
      constant := (6837254013564924034382651515840752974442969056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428866431493034531601/100000000000000000000)
  centralHi := (214433215746517265801/50000000000000000000)
  directionLo := (431754453561870988517/100000000000000000000)
  directionHi := (215877226780935494259/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree076.table
  base := (50020379224819793523337013175574154960171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-59321590202386915176013814949300000000000000)
      constant := (1299993067943669980819624980522993558965964659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree076.table
  base := (50020379205714890568428865556456124401849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-14382721727846552648499289734434850000000000000)
      constant := (315747380487355555983422646118436845304725396882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431754453561870988517/100000000000000000000)
  centralHi := (215877226780935494259/50000000000000000000)
  directionLo := (434623285477722583963/100000000000000000000)
  directionHi := (108655821369430645991/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree077.table
  base := (5221885015872017693085412305727219577539/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 364500000000000000000000000000000000000000
      center := (1566)
      previous := (0)
      next := (1350)
      square := (69494379852709832479096263255000000000000)
      linear := (-6006801131932342819153003407315000000000000)
      constant := (133365407218160928585758246864203893072025931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree077.table
  base := (52218850143525956071395040651313570432057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (345195)
      previous := (0)
      next := (296325)
      square := (15288763567596163145401177916100000000000000)
      linear := (-1323973594973568502204813718253112500000000000)
      constant := (29447555611524814209543002377950851808214330166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434623285477722583963/100000000000000000000)
  centralHi := (108655821369430645991/25000000000000000000)
  directionLo := (218736652386145652089/50000000000000000000)
  directionHi := (437473304772291304179/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree078.table
  base := (5445923159602540348815507705526539734487/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40500000000000000000000000000000000000000
      center := (174)
      previous := (0)
      next := (150)
      square := (7721597761412203608788473695000000000000)
      linear := (-675715915958443791189402813300000000000000)
      constant := (15197183166239468691613892762792649718493447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree078.table
  base := (13614807895985851167798137586007493111137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1638299706841328266667401340792625000000000000)
      constant := (36911513814161767202041653707619380207358029896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218736652386145652089/50000000000000000000)
  centralHi := (437473304772291304179/100000000000000000000)
  directionLo := (220152438379257001361/50000000000000000000)
  directionHi := (440304876758514002723/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree079.table
  base := (56741523530956355436199214887403771080161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-61560853553196454222562472320850000000000000)
      constant := (1402270306279285693136287979205204849117437369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree079.table
  base := (113483047042701366368472515705173494224787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-14925685178434655275760273233483012500000000000)
      constant := (340588918288413540444086495090971846798949236483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220152438379257001361/50000000000000000000)
  centralHi := (440304876758514002723/100000000000000000000)
  directionLo := (443118355077140011747/100000000000000000000)
  directionHi := (110779588769285002937/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree080.table
  base := (118131451917564322961302065370108993773743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-124614549340265934476157382889400000000000000)
      constant := (2874451072262722026714249555966809456461058647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree080.table
  base := (118131451902292982730164564474068903555271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-15106672995297356151513934399832400000000000000)
      constant := (349078993608834110995407142736987643913706899639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443118355077140011747/100000000000000000000)
  centralHi := (110779588769285002937/25000000000000000000)
  directionLo := (222957041106134651073/50000000000000000000)
  directionHi := (445914082212269302147/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree081.table
  base := (30715919437800107879176539580463536094659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (290)
      previous := (0)
      next := (250)
      square := (12869329602353672681314122825000000000000)
      linear := (-1167661033093879263955461306825000000000000)
      constant := (27270595824350613763583684499953765474555793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree081.table
  base := (12286367773906294690009923888400497224681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6534000000000000000000000000000000000000000
      center := (28127)
      previous := (0)
      next := (24145)
      square := (1245751105507835515551207089460000000000000)
      linear := (-113241931941926348350130337527272500000000000)
      constant := (2649435928059609938720146303208751426991065654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222957041106134651073/50000000000000000000)
  centralHi := (445914082212269302147/100000000000000000000)
  directionLo := (448692389977978785061/100000000000000000000)
  directionHi := (224346194988989392531/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree082.table
  base := (127679724556326524174672978845137323749369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-127600233808011986538222259384800000000000000)
      constant := (3016860442855269666017630463481805109013290001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree082.table
  base := (1994995696041894716305922884058611128021/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-15468648629022757903021256732531175000000000000)
      constant := (366373488325494869931090690164152708042962680896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448692389977978785061/100000000000000000000)
  centralHi := (224346194988989392531/50000000000000000000)
  directionLo := (11286339999449852867/2500000000000000000)
  directionHi := (451453599977994114681/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree083.table
  base := (132579592327486883487333784022700840580107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-129093076041885012569254697632500000000000000)
      constant := (3089359353734954947346530854840523912782898003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree083.table
  base := (66289796159911624240856129020411514165901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-15649636445885458778774917898880562500000000000)
      constant := (375177907720707010990149995097343040927994922618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11286339999449852867/2500000000000000000)
  centralHi := (451453599977994114681/100000000000000000000)
  directionLo := (454198024040209644909/100000000000000000000)
  directionHi := (45419802404020964491/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree084.table
  base := (137563281060050745149696197726974032147793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-14509546475084226511143015097800000000000000)
      constant := (351413453518394033697266628652684896603971233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree084.table
  base := (27512656210792498840315291716335294461739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (84381)
      previous := (0)
      next := (72435)
      square := (3737253316523506546653621268380000000000000)
      linear := (-351791650283292436767301757005110000000000000)
      constant := (8535269077184099879427208827089805971019503939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454198024040209644909/100000000000000000000)
  centralHi := (45419802404020964491/10000000000000000000)
  directionLo := (114231491156929606259/25000000000000000000)
  directionHi := (456925964627718425037/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree085.table
  base := (17828848843755507698471131634848965172773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-16509845063703883078914946765987500000000000)
      constant := (404618203330518331640349663990976770610951517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree085.table
  base := (142630790745208034397450436017516582827131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-16011612079610860530282240231579337500000000000)
      constant := (393101090582884102586407832535876821426473398379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114231491156929606259/25000000000000000000)
  centralHi := (456925964627718425037/100000000000000000000)
  directionLo := (229818857613942942611/50000000000000000000)
  directionHi := (459637715227885885223/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree086.table
  base := (36945530348504272205117088058167217508197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (7830)
      previous := (0)
      next := (6750)
      square := (347471899263549162395481316275000000000000)
      linear := (-33392900685876022665588003093900000000000000)
      constant := (828008247167060283381628395643028901563475613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree086.table
  base := (73891060695088130586305280400820094634837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-16192599896473561406035901397928725000000000000)
      constant := (402219854049207370357738206409164559142788673866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229818857613942942611/50000000000000000000)
  centralHi := (459637715227885885223/100000000000000000000)
  directionLo := (4623335607208839117/1000000000000000000)
  directionHi := (462333560720883911701/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree087.table
  base := (153017272988940115096822044843117342729687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3480)
      previous := (0)
      next := (3000)
      square := (154431955228244072175769473900000000000000)
      linear := (-15007160553041901854820494513700000000000000)
      constant := (376442574192846787180009982789467504761104647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree087.table
  base := (153017272985890098583775341801851198553527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1819287523704029142421062507142012500000000000)
      constant := (45715933207999076999592733531958288518898118127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4623335607208839117/1000000000000000000)
  centralHi := (462333560720883911701/100000000000000000000)
  directionLo := (465013777728995231791/100000000000000000000)
  directionHi := (29063361108062201987/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree088.table
  base := (79168122766060649601067839449706256570061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (15660)
      previous := (0)
      next := (13500)
      square := (694943798527098324790962632550000000000000)
      linear := (-68278643605625071362208444435500000000000000)
      constant := (1732398081922162077079006922005635861039574469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree088.table
  base := (79168122764849794446157250611265835357103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (345195)
      previous := (0)
      next := (296325)
      square := (15288763567596163145401177916100000000000000)
      linear := (-1504961411836269377958474884602500000000000000)
      constant := (38251975004636665489093652772471206467457217914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465013777728995231791/100000000000000000000)
  centralHi := (29063361108062201987/6250000000000000000)
  directionLo := (116919658736975107291/25000000000000000000)
  directionHi := (93535726989580085833/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree089.table
  base := (163739039021141881443884595342712040764457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-138050129445123168755449327118700000000000000)
      constant := (3542471976992587066324435102836412077717289153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree089.table
  base := (10233689938701205871020269887810359021053/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-16735563347061664033296884896976887500000000000)
      constant := (430204832586031835394001577224614115139084025232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116919658736975107291/25000000000000000000)
  centralHi := (93535726989580085833/20000000000000000000)
  directionLo := (94065678692214121181/20000000000000000000)
  directionHi := (235164196730535302953/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree090.table
  base := (169225653453805047271763828461767446186863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (51477318409414690725256491300000000000000)
      linear := (-5168258210333192399499324643200000000000000)
      constant := (134111503969585494196747455613967721047045301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree090.table
  base := (84612826726139452151495734091688048144061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (6228755527539177577756035447300000000000000)
      linear := (-626538931997198700335205409752825000000000000)
      constant := (16286767462106881378342738571233128769073294574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94065678692214121181/20000000000000000000)
  centralHi := (235164196730535302953/50000000000000000000)
  directionLo := (472963307038306909617/100000000000000000000)
  directionHi := (236481653519153454809/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree091.table
  base := (174796088828095522010419871479371606173013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-141035813912869220817514203614100000000000000)
      constant := (3700412054401518849882919733792836900900126477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree091.table
  base := (174796088826884224806509482457036291119953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-17097538980787065784804207229675662500000000000)
      constant := (449385391723389299880642470295601977875274934177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472963307038306909617/100000000000000000000)
  centralHi := (236481653519153454809/50000000000000000000)
  directionLo := (118895905604848286007/25000000000000000000)
  directionHi := (475583622419393144029/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree092.table
  base := (11278146571384225137862380042163507311333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 911250000000000000000000000000000000000000
      center := (3915)
      previous := (0)
      next := (3375)
      square := (173735949631774581197740658137500000000000)
      linear := (-17816082018342780856068330232725000000000000)
      constant := (472584539832419811027330570526374393659923514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree092.table
  base := (90225172570593156825216503775564570316619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-17278526797649766660557868396025050000000000000)
      constant := (459132843325379250083244515656876469116117290742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118895905604848286007/25000000000000000000)
  centralHi := (475583622419393144029/100000000000000000000)
  directionLo := (119547394895939711763/25000000000000000000)
  directionHi := (478189579583758847053/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree093.table
  base := (1454597049954842355047268100222084391631/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 101250000000000000000000000000000000000000
      center := (435)
      previous := (0)
      next := (375)
      square := (19303994403530509021971184237500000000000)
      linear := (-2000298588619656567771931668187500000000000)
      constant := (53636158332653579573682201379734696371553776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree093.table
  base := (186188422393457030507013318011665289060849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-1939946068279163059590169951374937500000000000)
      constant := (52109452920300356699209965575949667044960381049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119547394895939711763/25000000000000000000)
  centralHi := (478189579583758847053/100000000000000000000)
  directionLo := (120195353001746745667/25000000000000000000)
  directionHi := (480781412006986982669/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree094.table
  base := (9600516029133741757064187064533496731281/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 364500000000000000000000000000000000000000
      center := (1566)
      previous := (0)
      next := (1350)
      square := (69494379852709832479096263255000000000000)
      linear := (-7275717030724414945530575917860000000000000)
      constant := (197189664913771147446815482990329919117103849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree094.table
  base := (9600516029103481188908544554371027279467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176418000000000000000000000000000000000000000
      center := (759429)
      previous := (0)
      next := (651915)
      square := (33635279848711558919882591415420000000000000)
      linear := (-3528100486275033682413038145744765000000000000)
      constant := (95788418119043537275572599450650169218678018412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120195353001746745667/25000000000000000000)
  centralHi := (480781412006986982669/100000000000000000000)
  directionLo := (483359346904942242279/100000000000000000000)
  directionHi := (12083983672623556057/2500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree095.table
  base := (197916039705963412345217576366483035341307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-147007182848361324941643956604900000000000000)
      constant := (4026646013631324757752379358668541132763812803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree095.table
  base := (98958019852741640821255938099707367172391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-17821490248237869287818851895073212500000000000)
      constant := (489003886262786764868211106700266734848693875438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483359346904942242279/100000000000000000000)
  centralHi := (12083983672623556057/2500000000000000000)
  directionLo := (97184721093248485679/20000000000000000000)
  directionHi := (121480901366560607099/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree096.table
  base := (40781115952522332221869477301665529448213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (696)
      previous := (0)
      next := (600)
      square := (30886391045648814435153894780000000000000)
      linear := (-3300000557382985577170586552280000000000000)
      constant := (91341367689281970856063730275834907885305253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree096.table
  base := (101952789881115401253226426420041984102141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (421905)
      previous := (0)
      next := (362175)
      square := (18686266582617532733268106341900000000000000)
      linear := (-2000275340566730018174723673491400000000000000)
      constant := (55463384809475669486507290953893662972370167882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97184721093248485679/20000000000000000000)
  centralHi := (121480901366560607099/25000000000000000000)
  directionLo := (244237201536873042791/50000000000000000000)
  directionHi := (488474403073746085583/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree097.table
  base := (1679831526009686408632135516997360744813/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1458000000000000000000000000000000000000000
      center := (6264)
      previous := (0)
      next := (5400)
      square := (277977519410839329916385053020000000000000)
      linear := (-29998573463221475400741766620060000000000000)
      constant := (838987979086697548073846155568791899574216925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree097.table
  base := (104989470375454360896794713927919930804811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-18183465881963271039326174227771987500000000000)
      constant := (509441821662576669702106477791894663899598146998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell178.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244237201536873042791/50000000000000000000)
  centralHi := (488474403073746085583/100000000000000000000)
  directionLo := (98202389903136815683/20000000000000000000)
  directionHi := (30688246844730254901/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree098.table
  base := (216136122670408944065516857053038459441253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (31320)
      previous := (0)
      next := (27000)
      square := (1389887597054196649581925265100000000000000)
      linear := (-151485709549980403034741271348000000000000000)
      constant := (4280381061877736386801898967917765036932673437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree098.table
  base := (216136122670169374320173689801467258720493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3797145)
      previous := (0)
      next := (3259575)
      square := (168176399243557794599412957077100000000000000)
      linear := (-18364453698825971915079835394121375000000000000)
      constant := (519817961394554821640640464800150842611975967037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell178.Kernel098
