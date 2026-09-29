import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell216.Parameters
import ForestUnimodality.BinomialMassData.Q49_89.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_89.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_89.Batch100_149
import ForestUnimodality.BinomialMassData.Q49_89.Batch150_199
import ForestUnimodality.BinomialMassData.Q99_179.Batch000_049
import ForestUnimodality.BinomialMassData.Q99_179.Batch050_099
import ForestUnimodality.BinomialMassData.Q99_179.Batch100_149
import ForestUnimodality.BinomialMassData.Q99_179.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel000
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
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree000.table
  base := (84586162720518150828752369/2500000000000000000000000)
  polynomial :=
    { denominator := 222500000000000000000000000000000000000000
      center := (931)
      previous := (0)
      next := (760)
      square := (13148929380142778903378664255000000000000)
      linear := (-58684813494681053458457142475000000000000)
      constant := (7528168482126115423758960841000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree000.table
  base := (84586162720518150828752369/2500000000000000000000000)
  polynomial :=
    { denominator := 447500000000000000000000000000000000000000
      center := (1881)
      previous := (0)
      next := (1520)
      square := (26445599539837723861851470805000000000000)
      linear := (-118029006916268635607458747225000000000000)
      constant := (15140923126972748998346674051000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel001
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
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree001.table
  base := (190940619991557044487634543230045580652623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-26046173921122424361335179109060000000000000)
      constant := (1525361776844899838657534959451471044349426783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree001.table
  base := (190272516362378287735744697664544356623999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-105453683787599820393526827890660000000000000)
      constant := (6149053213027368215065460276303945730589551959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24858765878532948431/50000000000000000000)
  directionHi := (49717531757065896863/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree002.table
  base := (58016547806213936767131577137624626162979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-15600277119069196845729807748510000000000000)
      constant := (473889103511616085196555107634584663836956659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree002.table
  base := (57679735388290274198045224554771495109821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-63199299311575648846056596384110000000000000)
      constant := (1906439947358177291327942212926893474813774661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24858765878532948431/50000000000000000000)
  centralHi := (49717531757065896863/100000000000000000000)
  directionLo := (8788900962319705701/12500000000000000000)
  directionHi := (70311207698557645609/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree003.table
  base := (38202314335141099157065795604014992508139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-18177467277577181510792025942490000000000000)
      constant := (326238928026774388708963208572362755656969019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree003.table
  base := (18969114708062967840244458947864621326597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-36835878364675693747674889411445000000000000)
      constant := (655876085838694352898487154774010331925494477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8788900962319705701/12500000000000000000)
  centralHi := (70311207698557645609/100000000000000000000)
  directionLo := (1076416137876966119/1250000000000000000)
  directionHi := (86113291030157289521/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree004.table
  base := (54185604036340831656272046552343090338481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-41509314872170332351708488272940000000000000)
      constant := (497915502500789718150747562060389618571108001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree004.table
  base := (3443057927028775754642263209655379283/640000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-168288428294254252289285922523340000000000000)
      constant := (2003365091799270093973736032831655118853171875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076416137876966119/1250000000000000000)
  centralHi := (86113291030157289521/100000000000000000000)
  directionLo := (3977402540565271749/4000000000000000000)
  directionHi := (49717531757065896863/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree005.table
  base := (8151357232943944359191602584491058844093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-46663695189186301681832924660900000000000000)
      constant := (415818181606007418563174985013768385520303265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree005.table
  base := (20235548239281535733425693773062452578507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-94616671564902864793936143700450000000000000)
      constant := (837616287001464610984961245600194043067942787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3977402540565271749/4000000000000000000)
  centralHi := (49717531757065896863/50000000000000000000)
  directionLo := (27792945170575976389/25000000000000000000)
  directionHi := (111171780682303905557/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree006.table
  base := (6385957622280750262540342160086800468993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-51818075506202271011957361048860000000000000)
      constant := (373009680385658133567524984443317732574467765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree006.table
  base := (31711561720960814653385186466387535811453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-210178257965357206886458652278460000000000000)
      constant := (1505020132310631989373223906170603034934765573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27792945170575976389/25000000000000000000)
  centralHi := (111171780682303905557/100000000000000000000)
  directionLo := (3805705752357182261/3125000000000000000)
  directionHi := (121782584075429832353/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree007.table
  base := (1282051975652947633324651192644433215303/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-14243113955804560085520449359205000000000000)
      constant := (88286114497943376569844357218062777492075315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree007.table
  base := (6366562459625042625429700413160244221781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-57780793200227171046261254289005000000000000)
      constant := (356737491200968351030268685796447385110085021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/3125000000000000000)
  centralHi := (121782584075429832353/100000000000000000000)
  directionLo := (16442528103644064359/12500000000000000000)
  directionHi := (131540224829152514873/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree008.table
  base := (10425679980875877769593525544311456048133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-31063418070117104836103116912390000000000000)
      constant := (173995583206555863104353278774651043357261493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree008.table
  base := (5176286805839907502423341322811046175819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-63017021909115040370907845508395000000000000)
      constant := (352004851368611124068825679657268730519416579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16442528103644064359/12500000000000000000)
  centralHi := (131540224829152514873/100000000000000000000)
  directionLo := (8788900962319705701/6250000000000000000)
  directionHi := (140622415397115291217/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree009.table
  base := (265925743149499034633631157229730638293/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-16820304114312544750582667553185000000000000)
      constant := (88315142283034060789271365848037142174701648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree009.table
  base := (16892949290868642263706297224084677271201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-273013002472011638782217746911140000000000000)
      constant := (1431076760124916144013167561654377144446551241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8788900962319705701/6250000000000000000)
  centralHi := (140622415397115291217/100000000000000000000)
  directionLo := (37288148817799422647/25000000000000000000)
  directionHi := (149152595271197690589/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree010.table
  base := (13848149150946102800621224166119395001247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-72435596774266148332455106600700000000000000)
      constant := (366603668556119224374710975988831727804877487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree010.table
  base := (13736843173949952560379143011981804661019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-293957917307563116080804111788700000000000000)
      constant := (1486740011681266029383720213575909003143709779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37288148817799422647/25000000000000000000)
  centralHi := (149152595271197690589/100000000000000000000)
  directionLo := (157220639994081437583/100000000000000000000)
  directionHi := (9826289999630089849/6250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree011.table
  base := (11164664875611373108329256391733995023461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-77589977091282117662579542988660000000000000)
      constant := (386646964439349375615530893797804974580834581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree011.table
  base := (1383191190396249061772773497165010975473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-78725708035778648344847619166565000000000000)
      constant := (392380139422073296776345771602048233330260786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/100000000000000000000)
  centralHi := (9826289999630089849/6250000000000000000)
  directionLo := (164894398340766614483/100000000000000000000)
  directionHi := (41223599585191653621/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree012.table
  base := (2214852974249119557183022265470442982353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-20686089352074521748175994844155000000000000)
      constant := (103131008829383835998488652782571378863218113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree012.table
  base := (877074147237936625435896473862097262611/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-167923873489333035338988420771910000000000000)
      constant := (837974709743852413002854104390637291956595255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164894398340766614483/100000000000000000000)
  centralHi := (41223599585191653621/25000000000000000000)
  directionLo := (1076416137876966119/625000000000000000)
  directionHi := (172226582060314579041/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree013.table
  base := (428621687306450549670047846786954068131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-21974684431328514080707103941145000000000000)
      constant := (110911304114832278278278020634027852694662604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree013.table
  base := (1694650197727261325924156515866041170941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-89198165453554386994140801605345000000000000)
      constant := (450914866172658650680964685630293825158120581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076416137876966119/625000000000000000)
  centralHi := (172226582060314579041/100000000000000000000)
  directionLo := (44814777509902584277/25000000000000000000)
  directionHi := (179259110039610337109/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree014.table
  base := (2553085076943551320301467843058508195111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-46526559021165012826476426076270000000000000)
      constant := (239790990797434549079277101176206443413474231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree014.table
  base := (1007056362451922564201564109359089868157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-377737576649769025275149571298940000000000000)
      constant := (1950926065116774702892170761258552992328092185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44814777509902584277/25000000000000000000)
  centralHi := (179259110039610337109/100000000000000000000)
  directionLo := (186025969950993626101/100000000000000000000)
  directionHi := (93012984975496813051/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree015.table
  base := (3562755152984648581076385486531956769233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-98207498359345994983077288540500000000000000)
      constant := (520006985775429327031502133580819629569094593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree015.table
  base := (1749794328296292234947628319356387975359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-199341245742660251286867968088250000000000000)
      constant := (1058214631790110124944069323221498027118477719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186025969950993626101/100000000000000000000)
  centralHi := (93012984975496813051/50000000000000000000)
  directionLo := (3851103450193091839/2000000000000000000)
  directionHi := (192555172509654591951/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree016.table
  base := (439006425345966310062299622963313486443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-103361878676361964313201724928460000000000000)
      constant := (564661450980811494395519481271142030630575015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree016.table
  base := (1069458026721991023423522457398340364647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-209813703160435989936161150527030000000000000)
      constant := (1149562177305017459046518974513340223623654527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851103450193091839/2000000000000000000)
  centralHi := (192555172509654591951/100000000000000000000)
  directionLo := (198870127028263587451/100000000000000000000)
  directionHi := (49717531757065896863/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree017.table
  base := (488300139060537769376224070746936343757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-54258129496688966821663080658210000000000000)
      constant := (306668128248983058339457276098246482778899197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree017.table
  base := (463450808830496496227456569332981470371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-220286160578211728585454332965810000000000000)
      constant := (1249083330511768720145434109141858059292157211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198870127028263587451/100000000000000000000)
  centralHi := (49717531757065896863/25000000000000000000)
  directionLo := (204990634879383090851/100000000000000000000)
  directionHi := (51247658719845772713/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree018.table
  base := (-114164247752159729915392496872633851497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-113670639310393902973450597704380000000000000)
      constant := (665860119772146804352999177466391867262292263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree018.table
  base := (-31609536614778958216674644384330042887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-461517235991974934469495030809180000000000000)
      constant := (2712864320472242411355948057566528405479288165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204990634879383090851/100000000000000000000)
  centralHi := (51247658719845772713/25000000000000000000)
  directionLo := (8437344923826917473/4000000000000000000)
  directionHi := (105466811547836468413/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree019.table
  base := (-68444697817317994507780768206603394933/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-29706254906852468075893758523085000000000000)
      constant := (180522905383319159511292943540861978034942828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree019.table
  base := (-566877287344131815441279931023274527771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-241231075413763205884040697843370000000000000)
      constant := (1471323137497352082972596950029523260855689389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8437344923826917473/4000000000000000000)
  centralHi := (105466811547836468413/50000000000000000000)
  directionLo := (1354460604070777657/625000000000000000)
  directionHi := (216713696651324425121/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree020.table
  base := (-1981062628936738553321973056321319407051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-123979399944425841633699470480300000000000000)
      constant := (781913450542942940725945690394878828976749029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree020.table
  base := (-402999123126538278160296244891229550349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-503407065663077889066667760564300000000000000)
      constant := (3187039068881607738722704831381200569886338455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1354460604070777657/625000000000000000)
  centralHi := (216713696651324425121/100000000000000000000)
  directionLo := (222343561364607811113/100000000000000000000)
  directionHi := (111171780682303905557/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree021.table
  base := (-556865094598045493282542672521153112021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-129133780261441810963823906868260000000000000)
      constant := (845228029319731856041301383002279730998408295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree021.table
  base := (-2814053391994306925880090607906163466101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-524351980498629366365254125441860000000000000)
      constant := (3445649155792135434044145707887558616382657859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222343561364607811113/100000000000000000000)
  centralHi := (111171780682303905557/50000000000000000000)
  directionLo := (113917176321562648801/50000000000000000000)
  directionHi := (227834352643125297603/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree022.table
  base := (-2812133056922292271998716222649421599/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-67144080289228890146974171628110000000000000)
      constant := (455977033809805104013412464161906207196450625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree022.table
  base := (-3541152513789779610815643981753806555273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-545296895334180843663840490319420000000000000)
      constant := (3718148928996743148474841751063946284162497807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113917176321562648801/50000000000000000000)
  centralHi := (227834352643125297603/100000000000000000000)
  directionLo := (9327835779714549091/4000000000000000000)
  directionHi := (58298973623215931819/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree023.table
  base := (-1045535618511442593367715191464563547747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-34860635223868437406018194911045000000000000)
      constant := (245505945766089529856283386543789192138296013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree023.table
  base := (-4204811607419369329956648079537793100901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-566241810169732320962426855196980000000000000)
      constant := (4004265443186940155060382456661049571254031059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9327835779714549091/4000000000000000000)
  centralHi := (58298973623215931819/25000000000000000000)
  directionLo := (238436906061837849903/100000000000000000000)
  directionHi := (14902306628864865619/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree024.table
  base := (-1198098236594770707881396406606839657783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-36149230303122429738549304008035000000000000)
      constant := (263845156879614142299893593183787223070700857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree024.table
  base := (-2406065685499938734330784129194356654897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-293593362502641899130506610037270000000000000)
      constant := (2151885592447183010306248618085523618420445223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238436906061837849903/100000000000000000000)
  centralHi := (14902306628864865619/6250000000000000000)
  directionLo := (3805705752357182261/1562500000000000000)
  directionHi := (48713033630171932941/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree025.table
  base := (-214075011370949739769065897601654108171/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-149751301529505688284321652420100000000000000)
      constant := (1131977411259081585431259849492432445229437725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree025.table
  base := (-671129026165967407755291466249237596227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-152032909960208818889899896238025000000000000)
      constant := (1154119114607234540940741207451066356358581386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/1562500000000000000)
  centralHi := (48713033630171932941/20000000000000000000)
  directionLo := (124293829392664742157/50000000000000000000)
  directionHi := (49717531757065896863/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree026.table
  base := (-5865561927645366329106975919042995844879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-154905681846521657614446088808060000000000000)
      constant := (1211774747589661589883361640195540429912713441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree026.table
  base := (-5880451194270446911292898044592918911269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-629076554676386752858185949829660000000000000)
      constant := (4942223075070950266893329579611478285164029971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124293829392664742157/50000000000000000000)
  centralHi := (49717531757065896863/20000000000000000000)
  directionLo := (126755332298473991171/50000000000000000000)
  directionHi := (253510664596947982343/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree027.table
  base := (-3168801750356195229961577179272474218899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-80030031081768813472285262598010000000000000)
      constant := (647369879707881163128301924281942731712101021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree027.table
  base := (-6350505754157090522209595379607588072779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-650021469511938230156772314707220000000000000)
      constant := (5280879108299309953923771334459913270560088061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126755332298473991171/50000000000000000000)
  centralHi := (253510664596947982343/100000000000000000000)
  directionLo := (258339873090471868561/100000000000000000000)
  directionHi := (129169936545235934281/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree028.table
  base := (-27085859309681581016648125365091434277/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-82607221240276798137347480791990000000000000)
      constant := (690422500933455430190561573486848843636485375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree028.table
  base := (-26494648137551965469219498678061133967/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-167741596086872426863839669896195000000000000)
      constant := (1408083632055848428952030770553779565220054592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258339873090471868561/100000000000000000000)
  centralHi := (129169936545235934281/50000000000000000000)
  directionLo := (52616089931661005949/20000000000000000000)
  directionHi := (131540224829152514873/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree029.table
  base := (-1434007667238882591610030128424239180133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-170368822797569565604819397971940000000000000)
      constant := (1470067564017552511834559082184038007270832535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree029.table
  base := (-3589843925654329445071905736408616628123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-345955649591520592376972522231170000000000000)
      constant := (2998248782308615264962951476067871514618310957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52616089931661005949/20000000000000000000)
  centralHi := (131540224829152514873/50000000000000000000)
  directionLo := (26773710231574334981/10000000000000000000)
  directionHi := (267737102315743349811/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree030.table
  base := (-1883934666149477601128760207069354419549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-43880800778646383733735958589975000000000000)
      constant := (390597079880886764958323175103553643642752371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree030.table
  base := (-1886017104234066134561273406632706927553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-178214053504648165513132852334975000000000000)
      constant := (1593322918856255690116594488001831437334274327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26773710231574334981/10000000000000000000)
  centralHi := (267737102315743349811/100000000000000000000)
  directionLo := (68078534117061120339/25000000000000000000)
  directionHi := (272314136468244481357/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree031.table
  base := (-393529080265631516552476150826914551139/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-45169395857900376066267067686965000000000000)
      constant := (414447825322765605038410841399520049202139905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree031.table
  base := (-984720513995648141693154516992495962767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-183450282213536034837779443554365000000000000)
      constant := (1690663254803698423707868944072106873713965106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68078534117061120339/25000000000000000000)
  centralHi := (272314136468244481357/100000000000000000000)
  directionLo := (27681550152486138351/10000000000000000000)
  directionHi := (276815501524861383511/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree032.table
  base := (-4088124998512953060368706794083841276671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-92915981874308736797596353567910000000000000)
      constant := (878131589777428112534102084089821893247489009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree032.table
  base := (-4091218411770346788792362764007324215099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-377373021844847808324852069547510000000000000)
      constant := (3582264173730260821991468848084201324824012941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27681550152486138351/10000000000000000000)
  centralHi := (276815501524861383511/100000000000000000000)
  directionLo := (281244830794230582433/100000000000000000000)
  directionHi := (140622415397115291217/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree033.table
  base := (-4227074362370423986963938199310457885821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-95493172032816721462658571761890000000000000)
      constant := (928896413110409419340004690629921863086411859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree033.table
  base := (-4229736347315385863623976943582934976149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-387845479262623546974145251986290000000000000)
      constant := (3789436623377684750622165452435319180429209891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281244830794230582433/100000000000000000000)
  centralHi := (140622415397115291217/50000000000000000000)
  directionLo := (285605475809708954661/100000000000000000000)
  directionHi := (142802737904854477331/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree034.table
  base := (-8705450632206252179356028667144852452697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-196140724382649412255441579911740000000000000)
      constant := (1962370951193616045585988141345025623722187063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree034.table
  base := (-4355013939418983023401894784977258533847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-398317936680399285623438434425070000000000000)
      constant := (4002825336390879037677008295691283659317008273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285605475809708954661/100000000000000000000)
  centralHi := (142802737904854477331/50000000000000000000)
  directionLo := (1449502680029473961/500000000000000000)
  directionHi := (289900536005894792201/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree035.table
  base := (-8931134849361503914348476224438960111777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-201295104699665381585566016299700000000000000)
      constant := (2069989798784997975796536403650218996954614383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree035.table
  base := (-8935066701986363762088031612466696117511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-817580788196350048545463233727700000000000000)
      constant := (8444829727575957787508989918788954589698830049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1449502680029473961/500000000000000000)
  centralHi := (289900536005894792201/100000000000000000000)
  directionLo := (294132884493590683589/100000000000000000000)
  directionHi := (29413288449359068359/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree036.table
  base := (-1141502348560405711684572328446243506911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-51612371254170337728922613171915000000000000)
      constant := (545160723568080335988433607280974610363515938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree036.table
  base := (-570962093197170874513031305371832801387/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-209631425757975381461012399651315000000000000)
      constant := (2224096159923509449090979299638544420843036532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294132884493590683589/100000000000000000000)
  centralHi := (29413288449359068359/10000000000000000000)
  directionLo := (298305190542395381177/100000000000000000000)
  directionHi := (149152595271197690589/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree037.table
  base := (-9308784855185878555535743284624789969849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-211603865333697320245814889075620000000000000)
      constant := (2294324832320714479429283795686607038648826071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree037.table
  base := (-4655839561118707496681412032927673584789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-429735308933726501571317981741410000000000000)
      constant := (4680146956800733804925985137185024410669775651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298305190542395381177/100000000000000000000)
  centralHi := (149152595271197690589/50000000000000000000)
  directionLo := (75604984817698061759/25000000000000000000)
  directionHi := (302419939270792247037/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree038.table
  base := (-2365500686853877568599452876610431529923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-54189561412678322393984831365895000000000000)
      constant := (602757775088186565636586412078798771851479917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree038.table
  base := (-1892896632504050304391653451105973075747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-880415532703004480441222328360380000000000000)
      constant := (9836539620202841476133103933019287583399951865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75604984817698061759/25000000000000000000)
  centralHi := (302419939270792247037/100000000000000000000)
  directionLo := (61295889791262358899/20000000000000000000)
  directionHi := (4788741389942371789/1562500000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree039.table
  base := (-9592148071256883641606967450694623116477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-221912625967729258906063761851540000000000000)
      constant := (2530757931092619445653098504296727890294385683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree039.table
  base := (-1918854467847526864864030982028192422067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-901360447538555957739808693237940000000000000)
      constant := (10325106805090842281304308453633853433022756265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61295889791262358899/20000000000000000000)
  centralHi := (4788741389942371789/1562500000000000000)
  directionLo := (310485886308185323713/100000000000000000000)
  directionHi := (155242943154092661857/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree040.table
  base := (-4849808940972550497341295941975067610383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-113533503142372614118094099119750000000000000)
      constant := (1326751089732908391567025674289615489458156257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree040.table
  base := (-4850717971874890524949915051597184500207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-461152681187053717519197529057750000000000000)
      constant := (5412991497490498645829756676397774611428867513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310485886308185323713/100000000000000000000)
  centralHi := (155242943154092661857/50000000000000000000)
  directionLo := (157220639994081437583/50000000000000000000)
  directionHi := (314441279988162875167/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree041.table
  base := (-15655589852741327386526229313223514967/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-232221386601761197566312634627460000000000000)
      constant := (2779261219831273106940923895518902836216495625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree041.table
  base := (-4893149339903240783377541564082464186073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-471625138604829456168490711496530000000000000)
      constant := (5669578893020229745018139485855573765014035007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/50000000000000000000)
  centralHi := (314441279988162875167/100000000000000000000)
  directionLo := (12733901304760240341/4000000000000000000)
  directionHi := (159173766309503004263/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree042.table
  base := (-9847802132210648445195577998933398602119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-237375766918777166896437071015420000000000000)
      constant := (2908032860187694812806612572006168549672615401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree042.table
  base := (-9849131379988332519202699953614532646219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-964195192045210389635567787870620000000000000)
      constant := (11864622500522513979354051171161956759482497021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12733901304760240341/4000000000000000000)
  centralHi := (159173766309503004263/50000000000000000000)
  directionLo := (80551607870600552713/25000000000000000000)
  directionHi := (322206431482402210853/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree043.table
  base := (-9889024334190177346705978109389412106191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-242530147235793136226561507403380000000000000)
      constant := (3039815270550387688271158413756646466706861089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree043.table
  base := (-9890159944046091736107540951205022250263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-985140106880761866934154152748180000000000000)
      constant := (12402369900373246728018170959979559882079323217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80551607870600552713/25000000000000000000)
  centralHi := (322206431482402210853/100000000000000000000)
  directionLo := (163009829038496024159/50000000000000000000)
  directionHi := (326019658076992048319/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree044.table
  base := (-9908603138703775275594381503215754438863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-247684527552809105556685943791340000000000000)
      constant := (3174606923158046208556091376701908009089766177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree044.table
  base := (-12386965992708442635374475688943458211/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-251521255429078336058185129406435000000000000)
      constant := (3238098487089341058182888781861332531092269800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163009829038496024159/50000000000000000000)
  centralHi := (326019658076992048319/100000000000000000000)
  directionLo := (329788796681533228967/100000000000000000000)
  directionHi := (41223599585191653621/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree045.table
  base := (-9906699567733407188457597498900595125687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-252838907869825074886810380179300000000000000)
      constant := (3312406542555551229240208134230208386009433273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree045.table
  base := (-2476881773310576745073428021974656194749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-256757484137966205382831720625825000000000000)
      constant := (3378672402204661081747150494057660040864047291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329788796681533228967/100000000000000000000)
  centralHi := (41223599585191653621/12500000000000000000)
  directionLo := (33351534204691171667/10000000000000000000)
  directionHi := (333515342046911716671/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree046.table
  base := (-9883448051444928355752662132945996010383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-257993288186841044216934816567260000000000000)
      constant := (3453213063921559010726218503896414765601756257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree046.table
  base := (-4942076965693644718786782177007257229881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-523987425693708149414956623690430000000000000)
      constant := (7044626340749363531975665278096250471097382879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33351534204691171667/10000000000000000000)
  centralHi := (333515342046911716671/100000000000000000000)
  directionLo := (337200706322930727081/100000000000000000000)
  directionHi := (168600353161465363541/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree047.table
  base := (-9838960820235635437499644732037783582481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-263147668503857013547059252955220000000000000)
      constant := (3597025598279092566170103516563848716243167999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree047.table
  base := (-491978132594811407945059732667645588779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-267229941555741944032124903064605000000000000)
      constant := (3669019915732278128576381447314559838449660305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337200706322930727081/100000000000000000000)
  centralHi := (168600353161465363541/50000000000000000000)
  directionLo := (85211556327728455587/25000000000000000000)
  directionHi := (340846225310913822349/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree048.table
  base := (-9773331571350761995022634761340163617683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-268302048820872982877183689343180000000000000)
      constant := (3743843403452272400532615059578944563984332957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree048.table
  base := (-4886922229713771475078633472957490744221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-544932340529259626713542988567990000000000000)
      constant := (7637583815410670124525482660742729039064414939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85211556327728455587/25000000000000000000)
  centralHi := (340846225310913822349/100000000000000000000)
  directionLo := (344453164120629158081/100000000000000000000)
  directionHi := (172226582060314579041/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree049.table
  base := (-2421659632472032712965659855154761680631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-68364107284472238051827031432785000000000000)
      constant := (973416464955024664807121203728089132727721849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree049.table
  base := (-9687075429508998881532305064887985166061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1110809595894070730725672342013540000000000000)
      constant := (15886514147639425147573674578735004067294239499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344453164120629158081/100000000000000000000)
  centralHi := (172226582060314579041/50000000000000000000)
  directionLo := (8700568057486531951/2500000000000000000)
  directionHi := (348022722299461278041/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree050.table
  base := (-9578947004219713288418023344699198549501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-278610809454904921537432562119100000000000000)
      constant := (4046492450074956957745677336291637648289402579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree050.table
  base := (-9579319018699222153350236529218934729583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1131754510729622208024258706891100000000000000)
      constant := (16510117180171772267789074599372296112329431097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8700568057486531951/2500000000000000000)
  centralHi := (348022722299461278041/100000000000000000000)
  directionLo := (351556038492788228041/100000000000000000000)
  directionHi := (175778019246394114021/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree051.table
  base := (-73830558744821528303925694501337344901/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-70941297442980222716889249626765000000000000)
      constant := (1050580685581097116399405471825677020513253728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree051.table
  base := (-1890125631651590566328712796989109584171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1152699425565173685322845071768660000000000000)
      constant := (17145975032447888278241417966115639699067884945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351556038492788228041/100000000000000000000)
  centralHi := (175778019246394114021/50000000000000000000)
  directionLo := (17752709734344617387/5000000000000000000)
  directionHi := (355054194686892347741/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree052.table
  base := (-930077759783551441609266745182908270949/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-144459785044468430098840717447510000000000000)
      constant := (2180578187991958869883203385404990917929064855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree052.table
  base := (-581315437526910371879691102599814466419/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-293411085100181290655357859161555000000000000)
      constant := (4448521572446419779369278964670377378725875284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17752709734344617387/5000000000000000000)
  centralHi := (355054194686892347741/100000000000000000000)
  directionLo := (358518220079220674217/100000000000000000000)
  directionHi := (179259110039610337109/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree053.table
  base := (-1826076649346953511996659235490405917857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-294073950405952829527805871282980000000000000)
      constant := (4522993049999939535369541673723322473623273515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree053.table
  base := (-2282653093746551463408630000409092154991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-298647313809069159980004450380945000000000000)
      constant := (4613612443030627907884587503772122278261933369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358518220079220674217/100000000000000000000)
  centralHi := (179259110039610337109/50000000000000000000)
  directionLo := (361949094615233657427/100000000000000000000)
  directionHi := (90487273653808414357/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree054.table
  base := (-2234790049681465450442389046749107785333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-74807082680742199714482576917735000000000000)
      constant := (1171958128254452215805623391609770317232377307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree054.table
  base := (-6983871096941552453588166777698215453/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-303883542517957029304651041600335000000000000)
      constant := (4781766123772411795095480612801316873174536640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361949094615233657427/100000000000000000000)
  centralHi := (90487273653808414357/25000000000000000000)
  directionLo := (11417117257071546783/3125000000000000000)
  directionHi := (365347752226289497057/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree055.table
  base := (-8727134948402989353845668560592604630597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-304382711039984768188054744058900000000000000)
      constant := (4855674555173845126810887823781545978721041163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree055.table
  base := (-8727300515574454114652968824112051956069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1236479084907379594517190531278900000000000000)
      constant := (19811929637545241821572888203336625743275593171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11417117257071546783/3125000000000000000)
  centralHi := (365347752226289497057/100000000000000000000)
  directionLo := (92178770949720670391/25000000000000000000)
  directionHi := (73743016759776536313/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree056.table
  base := (-8494329617344212802200729178462348322373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-309537091357000737518179180446860000000000000)
      constant := (5026519001243028492391104817283479738938483467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree056.table
  base := (-1698894057631313972272245975168514591337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1257423999742931071815776896156460000000000000)
      constant := (20509044514494286731287256228062208119894855915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92178770949720670391/25000000000000000000)
  centralHi := (73743016759776536313/20000000000000000000)
  directionLo := (372051939901987252203/100000000000000000000)
  directionHi := (93012984975496813051/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree057.table
  base := (-8240762676309548589897813012814589198047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-314691471674016706848303616834820000000000000)
      constant := (5200365704918468869717641930090015638962269713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree057.table
  base := (-8240882156328321764787279134938171214667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1278368914578482549114363261034020000000000000)
      constant := (21218408554501670344952051109901966056110854653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372051939901987252203/100000000000000000000)
  centralHi := (93012984975496813051/25000000000000000000)
  directionLo := (37535913329616316937/10000000000000000000)
  directionHi := (375359133296163169371/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree058.table
  base := (-7966449548156405160297391348744957307363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-319845851991032676178428053222780000000000000)
      constant := (5377214544035712726510640869151911193168377677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree058.table
  base := (-7966550998356415285103143010009077516167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1299313829414034026412949625911580000000000000)
      constant := (21940021280852849152917900950697619147304493153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37535913329616316937/10000000000000000000)
  centralHi := (375359133296163169371/100000000000000000000)
  directionLo := (94659360311349309667/25000000000000000000)
  directionHi := (378637441245397238669/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree059.table
  base := (-3835701555587135167266294751820220385401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-162500116154024322754276244805370000000000000)
      constant := (2778532708292914514869453074415072034327238679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree059.table
  base := (-1534297845339421245489707906426197131819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1320258744249585503711535990789140000000000000)
      constant := (22673882295840312262932324045015471088496937105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94659360311349309667/25000000000000000000)
  centralHi := (378637441245397238669/100000000000000000000)
  directionLo := (7637752153006184109/2000000000000000000)
  directionHi := (381887607650309205451/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree060.table
  base := (-7355634119286373279635955421739841782121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-330154612625064614838676925998700000000000000)
      constant := (5739918237386991881170372956858398713243819559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree060.table
  base := (-58845657576372531266820211981106664729/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1341203659085136981010122355666700000000000000)
      constant := (23419991267657198633821912852003170169427263875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7637752153006184109/2000000000000000000)
  centralHi := (381887607650309205451/100000000000000000000)
  directionLo := (3851103450193091839/1000000000000000000)
  directionHi := (385110345019309183901/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree061.table
  base := (-3509575776424684143673946931982406940719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-167654496471040292084400681193330000000000000)
      constant := (2962886467652898111080082773562707354622564801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree061.table
  base := (-3509606774761502154864542616746360490607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-681074286960344229154354360272130000000000000)
      constant := (12089173959732740373808830747981769863520461113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851103450193091839/1000000000000000000)
  centralHi := (385110345019309183901/100000000000000000000)
  directionLo := (388306336292502718559/100000000000000000000)
  directionHi := (2426914601828141991/625000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree062.table
  base := (-1665490727878530878311167200462526277549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-85115843314774138374731449693655000000000000)
      constant := (1528657362734376881511991083178166329355534371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree062.table
  base := (-3331007746620710793508111153683942451937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-691546744378119967803647542710910000000000000)
      constant := (12474476010138952418138840404230872799897486583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388306336292502718559/100000000000000000000)
  centralHi := (2426914601828141991/625000000000000000)
  directionLo := (391476236531569141781/100000000000000000000)
  directionHi := (195738118265784570891/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree063.table
  base := (-6284074458717333967506805437715091713887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-345617753576112522829050235162580000000000000)
      constant := (6306487734669443731658129373492578758534301073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree063.table
  base := (-6284119043673437611341599865891061420027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1404038403591791412905881450299380000000000000)
      constant := (25731803377352744743531669366657704501040914893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391476236531569141781/100000000000000000000)
  centralHi := (195738118265784570891/50000000000000000000)
  directionLo := (197310337243728772309/50000000000000000000)
  directionHi := (394620674487457544619/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree064.table
  base := (-1471372856448260457911887515012913901437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-87693033473282123039793667887635000000000000)
      constant := (1625336936266051972717723561403502708986717523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree064.table
  base := (-2942764610313092686657380583045627290087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-712491659213671445102233907588470000000000000)
      constant := (13263450914925180060613753397526475055998322433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197310337243728772309/50000000000000000000)
  centralHi := (394620674487457544619/100000000000000000000)
  directionLo := (198870127028263587451/50000000000000000000)
  directionHi := (397740254056527174903/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree065.table
  base := (-5466218182373585447294524025819992299737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-355926514210144461489299107938500000000000000)
      constant := (6699209447509942251682226560308479840993783223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree065.table
  base := (-21352539895993881377432027658156400131/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-361482058315723591875763545013625000000000000)
      constant := (6833561810885549525884016339779770690137768256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198870127028263587451/50000000000000000000)
  centralHi := (397740254056527174903/100000000000000000000)
  directionLo := (400835555634683732551/100000000000000000000)
  directionHi := (50104444454335466569/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree066.table
  base := (-1256564594661972357349373708311965270057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-90270223631790107704855886081615000000000000)
      constant := (1725018203273375085554277302305630923095878503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree066.table
  base := (-2513142759197958840198752128592381560341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-733436574049222922400820272466030000000000000)
      constant := (14076919753198807786997086065050111502425114019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400835555634683732551/100000000000000000000)
  centralHi := (50104444454335466569/12500000000000000000)
  directionLo := (40390713737811132389/10000000000000000000)
  directionHi := (403907137378111323891/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree067.table
  base := (-4565615064125353009741679551584736623661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-366235274844176400149547980714420000000000000)
      constant := (7103937817659718211160571487950617301203981219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree067.table
  base := (-4565638054255578821646352385405256915357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1487818062933997322100226909809620000000000000)
      constant := (28985678524902873248248101804037950163175046363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40390713737811132389/10000000000000000000)
  centralHi := (403907137378111323891/100000000000000000000)
  directionLo := (406955536378355896803/100000000000000000000)
  directionHi := (101738884094588974201/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree068.table
  base := (-2042145393392919303997825608302256167101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-185694827580596184739836208551190000000000000)
      constant := (3655402220513023684143209314738197828900392979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree068.table
  base := (-4084310257430172663827667157981087950143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1508762977769548799398813274687180000000000000)
      constant := (29829764220990819399879275823290247960989468137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406955536378355896803/100000000000000000000)
  centralHi := (101738884094588974201/25000000000000000000)
  directionLo := (409981269758766181703/100000000000000000000)
  directionHi := (51247658719845772713/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree069.table
  base := (-716457535171063667441055331502156673009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-376544035478208338809796853490340000000000000)
      constant := (7520672666326888888487214322645737084965478555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree069.table
  base := (-358230416223561296069842589100497945901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-764853946302550138348699819782370000000000000)
      constant := (15343048264739968918151783438836094726576930295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409981269758766181703/100000000000000000000)
  centralHi := (51247658719845772713/12500000000000000000)
  directionLo := (206492417849315390813/50000000000000000000)
  directionHi := (412984835698630781627/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree070.table
  base := (-1529803755455828635026890242710939603527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-190849207897612154069960644939150000000000000)
      constant := (3866771239733103251261117372656986647400462633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree070.table
  base := (-1529810733747353148073085757145379804041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-775326403720325876997993002221150000000000000)
      constant := (15777337697969123505883317102084804885698722319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206492417849315390813/50000000000000000000)
  centralHi := (412984835698630781627/100000000000000000000)
  directionLo := (207983357195377484851/50000000000000000000)
  directionHi := (415966714390754969703/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree071.table
  base := (-2516251779578312962217511491706057941503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-386852796112240277470045726266260000000000000)
      constant := (7949413868660534803092967538704676315045354737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree071.table
  base := (-1258131796072641925238919832210153633927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-785798861138101615647286184659930000000000000)
      constant := (16217750387450779938710131639025394467415344993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207983357195377484851/50000000000000000000)
  centralHi := (415966714390754969703/100000000000000000000)
  directionLo := (52365921117211151727/12500000000000000000)
  directionHi := (418927368937689213817/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree072.table
  base := (-976110862845406614889392878642612202049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-196003588214628123400085081327110000000000000)
      constant := (4084143412028726287184112338570431868747569871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree072.table
  base := (-1952231721623704120406160784178742767239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1592542637111754708593158734197420000000000000)
      constant := (33328572628387310070671281503198448902994895201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52365921117211151727/12500000000000000000)
  centralHi := (418927368937689213817/100000000000000000000)
  directionLo := (8437344923826917473/2000000000000000000)
  directionHi := (421867246191345873651/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree073.table
  base := (-1367518389509551896480629279952073505121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-397161556746272216130294599042180000000000000)
      constant := (8390161337417057236870137651694019625765936559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree073.table
  base := (-1367526846554235900730557108638805005751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1613487551947306185891745099074980000000000000)
      constant := (34233890924654905395065520591778624048810732209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8437344923826917473/2000000000000000000)
  centralHi := (421867246191345873651/100000000000000000000)
  directionLo := (42478677754031431893/10000000000000000000)
  directionHi := (424786777540314318931/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree074.table
  base := (-190535660323135354417757889455297356841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-100578984265822046365104758857535000000000000)
      constant := (2153759350461508768484973759387394589636462439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree074.table
  base := (-23817181094402637739886590300515540767/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-408608116695714415797582865988135000000000000)
      constant := (8787863909292926559867476088175219452466276424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42478677754031431893/10000000000000000000)
  centralHi := (424786777540314318931/100000000000000000000)
  directionLo := (106921594912200542061/25000000000000000000)
  directionHi := (85537275929760433649/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree075.table
  base := (-136095209324788607406707436745686015803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-407470317380304154790543471818100000000000000)
      constant := (8842915011575640546603353596413537421068824437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree075.table
  base := (-136101259486412937339798920845741317833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1655377381618409140488917828830100000000000000)
      constant := (36081266743750513205114214544497181602435312847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106921594912200542061/25000000000000000000)
  centralHi := (85537275929760433649/20000000000000000000)
  directionLo := (430566455150786447601/100000000000000000000)
  directionHi := (215283227575393223801/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree076.table
  base := (102124659336035069917521549158864648583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-412624697697320124120667908206060000000000000)
      constant := (9073794161776332774346308699677716834407129715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree076.table
  base := (255309090376676739982304206413578903663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-838161148226980308893752096853830000000000000)
      constant := (18511662112915054381101071329143337481652266183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430566455150786447601/100000000000000000000)
  centralHi := (215283227575393223801/50000000000000000000)
  directionLo := (1354460604070777657/312500000000000000)
  directionHi := (433427393302648850241/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree077.table
  base := (1178012366042296179461202430025961847483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-417779078014336093450792344594020000000000000)
      constant := (9307674848403015047265588861077155643793912843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree077.table
  base := (1178008040839208695893932892296909427621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1697267211289512095086090558585220000000000000)
      constant := (37977628067875119086534633251411005274970404461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1354460604070777657/312500000000000000)
  centralHi := (433427393302648850241/100000000000000000000)
  directionLo := (218134785298645060787/50000000000000000000)
  directionHi := (17450782823891604863/4000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree078.table
  base := (1866071570802454794359551008276578300719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-422933458331352062780916780981980000000000000)
      constant := (9544557068065823183066298383273478776719995199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree078.table
  base := (933033957362199952917417645398564931551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-859106063062531786192338461731390000000000000)
      constant := (19472089128437700085749535160852675418971825591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218134785298645060787/50000000000000000000)
  centralHi := (17450782823891604863/4000000000000000000)
  directionLo := (439093351342466543309/100000000000000000000)
  directionHi := (43909335134246654331/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree079.table
  base := (160925034506418573383413113907302414119/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-107021959662092008027760304342485000000000000)
      constant := (2446110204480560831988711153112858969688946396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree079.table
  base := (2574797462141296187452972135737246664013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1739157040960615049683263288340340000000000000)
      constant := (39922974781928436854712939169964437120361640533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439093351342466543309/100000000000000000000)
  centralHi := (43909335134246654331/10000000000000000000)
  directionLo := (220949544102931801737/50000000000000000000)
  directionHi := (17675963528234544139/4000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree080.table
  base := (3304199008814532199296967124104669338691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-433242218965384001441165653757900000000000000)
      constant := (10027326095587036703773751918150033085831771411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree080.table
  base := (66083927954581460010741801293700527111/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-880050977898083263490924826608950000000000000)
      constant := (20457008816945491478541665513601286464729088775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220949544102931801737/50000000000000000000)
  centralHi := (17675963528234544139/4000000000000000000)
  directionLo := (444687122729215622227/100000000000000000000)
  directionHi := (111171780682303905557/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree081.table
  base := (4054266688044043503230270037506476164121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-438396599282399970771290090145860000000000000)
      constant := (10273212899057030598983052169242168797696002441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree081.table
  base := (4054264481963909401801682883921906530727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1781046870631718004280436018095460000000000000)
      constant := (41917306805088455731766434989466821807151023807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444687122729215622227/100000000000000000000)
  centralHi := (111171780682303905557/25000000000000000000)
  directionLo := (89491557162718614353/20000000000000000000)
  directionHi := (223728892906796535883/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree082.table
  base := (2412501688601939701679345205807033971203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-221775489799707970050707263266910000000000000)
      constant := (5261050613324160300452531115471457516085898963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree082.table
  base := (4825001513592676756251095616864236625917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1801991785467269481579022382973020000000000000)
      constant := (42932842289072503684168355275652467005731006597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89491557162718614353/20000000000000000000)
  centralHi := (223728892906796535883/50000000000000000000)
  directionLo := (225105699088904782217/50000000000000000000)
  directionHi := (90042279635561912887/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree083.table
  base := (1404102224348343762528739508184548279693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-112176339979107977357884740730445000000000000)
      constant := (2693497769235958635816589938972409806923448253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree083.table
  base := (2808203661660355139334606491606508290317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-911468350151410479438804373925290000000000000)
      constant := (21980312040209378229952991168031724132130046997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225105699088904782217/50000000000000000000)
  centralHi := (90042279635561912887/20000000000000000000)
  directionLo := (22647413539587310077/5000000000000000000)
  directionHi := (452948270791746201541/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree084.table
  base := (1285696619574159188850509093687077841731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-453859740233447878761663399309740000000000000)
      constant := (11028882448749547147098413000289956717921756255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree084.table
  base := (6428481768545635408693037296128547177401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1843881615138372436176195112728140000000000000)
      constant := (45000652174558091375690725361815734780111105441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22647413539587310077/5000000000000000000)
  centralHi := (452948270791746201541/100000000000000000000)
  directionLo := (113917176321562648801/25000000000000000000)
  directionHi := (91133741057250119041/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree085.table
  base := (3630612925718684227776697509724913068353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-229507060275231924045893917848850000000000000)
      constant := (5643387670528958463238132364554031036414424113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree085.table
  base := (1815306182240933921682352072879682341979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-466206632493480978368695369401425000000000000)
      constant := (11513231641908964263110189976221887901919349139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113917176321562648801/25000000000000000000)
  centralHi := (91133741057250119041/20000000000000000000)
  directionLo := (229186497170569997071/50000000000000000000)
  directionHi := (458372994341139994143/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree086.table
  base := (8114637050582546798748378466902118243323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-464168500867479817421912272085660000000000000)
      constant := (11547669753017352848234798177722211678605361483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree086.table
  base := (8114636102904136698411011299559430838371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1885771444809475390773367842483260000000000000)
      constant := (47117447256394417003045342835943063723492245211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229186497170569997071/50000000000000000000)
  centralHi := (458372994341139994143/100000000000000000000)
  directionLo := (461061422052721315139/100000000000000000000)
  directionHi := (23053071102636065757/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree087.table
  base := (4494358302132415193001272133101328826869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-234661440592247893376018354236810000000000000)
      constant := (5905782841953357593108886347473855625637629349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree087.table
  base := (28089736888344037518425870419617567763/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-476679089911256717017988551840205000000000000)
      constant := (12048553559518786343722398120387977319095542640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461061422052721315139/100000000000000000000)
  centralHi := (23053071102636065757/5000000000000000000)
  directionLo := (463734264282134395987/100000000000000000000)
  directionHi := (115933566070533598997/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree088.table
  base := (9883464435223203118095158346215736884797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-474477261501511756082161144861580000000000000)
      constant := (12078463133114019431903260846207094851864477037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree088.table
  base := (4941731879993342167035278660036705234693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-963830637240289172685270286119190000000000000)
      constant := (24641613755168324371780780127667596072424798413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463734264282134395987/100000000000000000000)
  centralHi := (115933566070533598997/25000000000000000000)
  directionLo := (466391788985727454551/100000000000000000000)
  directionHi := (58298973623215931819/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree089.table
  base := (1079888047773159532823379319507035736009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445000000000000000000000000000000000000000
      center := (1862)
      previous := (0)
      next := (1520)
      square := (26297858760285557806757328510000000000000)
      linear := (-2694559785497346771979132478930000000000000)
      constant := (69372820787183423525059549512240630902524005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree089.table
  base := (10798879907870959673520299212256696440157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1948606189316129822669126937115940000000000000)
      constant := (50384487071186523079645626651576596810639070437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466391788985727454551/100000000000000000000)
  centralHi := (58298973623215931819/12500000000000000000)
  directionLo := (469034256528584680471/100000000000000000000)
  directionHi := (58629282066073085059/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree090.table
  base := (11734964675723236041861954853244058267303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-484786022135543694742410017637500000000000000)
      constant := (12621262584476500160000327607209546185535307063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree090.table
  base := (11734964194854444760703679102130935948413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1969551104151681299967713301993500000000000000)
      constant := (51497992918924401431304648051968377318723100933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469034256528584680471/100000000000000000000)
  centralHi := (58629282066073085059/12500000000000000000)
  directionLo := (471661919982244312749/100000000000000000000)
  directionHi := (1886647679928977251/400000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree091.table
  base := (12691716981223840716288973726308363656859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-489940402452559664072534454025460000000000000)
      constant := (12897164585807567441659791434441768548525980139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree091.table
  base := (12691716575499619474854832800238753744897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-1990496018987232777266299666871060000000000000)
      constant := (52623745052094420216349165402016129908740244777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471661919982244312749/100000000000000000000)
  centralHi := (1886647679928977251/400000000000000000)
  directionLo := (14821094543986586347/3125000000000000000)
  directionHi := (94855005081514152621/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree092.table
  base := (6834568676521331171589751229003731452093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-247547391384787816701329445206710000000000000)
      constant := (6588034051892789662692983504233298556832028653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree092.table
  base := (2733827402152321724294300627994684361777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2011440933822784254564886031748620000000000000)
      constant := (53761743469445542588672131879844608408178484285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14821094543986586347/3125000000000000000)
  centralHi := (94855005081514152621/20000000000000000000)
  directionLo := (476873812123675699807/100000000000000000000)
  directionHi := (14902306628864865619/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree093.table
  base := (7333612877839425607207375278543426866711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-250124581543295801366391663400690000000000000)
      constant := (6728986569064666790320422694901402484211217831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree093.table
  base := (14667225466954442280165629339469894919689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2032385848658335731863472396626180000000000000)
      constant := (54911988169898436386054393629942074903121755249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476873812123675699807/100000000000000000000)
  centralHi := (14902306628864865619/3125000000000000000)
  directionLo := (239729256481859971593/50000000000000000000)
  directionHi := (479458512963719943187/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree094.table
  base := (15685982158407595826225758792336986503471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-505403543403607572062907763189340000000000000)
      constant := (13742879688595458975503072652379981270093993791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree094.table
  base := (15685981914887977222617355923288563078003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2053330763493887209162058761503740000000000000)
      constant := (56074479152517820229317354163019968849582294123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239729256481859971593/50000000000000000000)
  centralHi := (479458512963719943187/100000000000000000000)
  directionLo := (120507338629592508311/25000000000000000000)
  directionHi := (96405870903674006649/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree095.table
  base := (209067581681454799429847789652180887281/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-127639480930155885348258049894325000000000000)
      constant := (3507696938743091425161141228970198496163056020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree095.table
  base := (8362703164573598210385742253811616453309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1037137839164719343230322563190650000000000000)
      constant := (28624608208244685778932548433831378002780473669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120507338629592508311/25000000000000000000)
  centralHi := (96405870903674006649/20000000000000000000)
  directionLo := (242293278683814977153/50000000000000000000)
  directionHi := (484586557367629954307/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree096.table
  base := (8892749430333310286654734940086888205439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-257856152018819755361578317982630000000000000)
      constant := (7160848668537594372433806058102668241475282319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree096.table
  base := (555796833984071718849578061235501182369/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-523805148291247540939807872814715000000000000)
      constant := (14609049990275110175452941023353493547074281032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242293278683814977153/50000000000000000000)
  centralHi := (484586557367629954307/100000000000000000000)
  directionLo := (3805705752357182261/781250000000000000)
  directionHi := (487130336301719329409/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree097.table
  base := (9433129558179964024712134675978601171443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-260433342177327740026640536176610000000000000)
      constant := (7307804217370780229468367282387086499879000003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree097.table
  base := (1886625897034587401361002071719860397433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1058082754000270820528908928068210000000000000)
      constant := (29817714892861970233600036737448540234970753765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/781250000000000000)
  centralHi := (487130336301719329409/100000000000000000000)
  directionLo := (244830450265812028487/50000000000000000000)
  directionHi := (19586436021264962279/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree098.table
  base := (1996768728349186751639827952212502927969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-263010532335835724691702754370590000000000000)
      constant := (7456260523914037791295850553243636178462212245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree098.table
  base := (19967687160392827124351996936857795375731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2137110422836093118356404221013980000000000000)
      constant := (60846905889804885286184507932822380621633796971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244830450265812028487/50000000000000000000)
  centralHi := (19586436021264962279/4000000000000000000)
  directionLo := (246089226944951759629/50000000000000000000)
  directionHi := (492178453889903519259/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree099.table
  base := (21089783345978670070999189027434790330913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-531175444988687418713529945129140000000000000)
      constant := (15212435176207334582350008603036390974211161873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree099.table
  base := (2108978324220922777354490294089558078589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1079027668835822297827495292945770000000000000)
      constant := (31035314136424570604898135070517657651980350745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246089226944951759629/50000000000000000000)
  centralHi := (492178453889903519259/100000000000000000000)
  directionLo := (494683195022299843451/100000000000000000000)
  directionHi := (123670798755574960863/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree100.table
  base := (889301891577797821053810242290754415921/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-536329825305703388043654381517100000000000000)
      constant := (15515350819765469992541366777539626643212756025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree100.table
  base := (1111627360098939743642695626786250127557/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-544750063126799018238394237692275000000000000)
      constant := (15826649233603505193921005983366791201685269185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494683195022299843451/100000000000000000000)
  centralHi := (123670798755574960863/25000000000000000000)
  directionLo := (124293829392664742157/25000000000000000000)
  directionHi := (497175317570658968629/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree101.table
  base := (23395979100962322656462465533650598635199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-541484205622719357373778817905060000000000000)
      constant := (15821267978400076184684835456564326391789411279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree101.table
  base := (935839161089816368254862124629987142309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2199945167342747550252163315646660000000000000)
      constant := (64554811874100417468050877980362015450668066725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124293829392664742157/25000000000000000000)
  centralHi := (497175317570658968629/100000000000000000000)
  directionLo := (499655010347640217221/100000000000000000000)
  directionHi := (249827505173820108611/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree102.table
  base := (4916015753766126611239240090528243773249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-546638585939735326703903254293020000000000000)
      constant := (16130186652018476124843184918822291094639526645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree102.table
  base := (24580078706707732414348596030530268233893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2220890082178299027550749680524220000000000000)
      constant := (65815273091546225104512107246531140324482165613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499655010347640217221/100000000000000000000)
  centralHi := (249827505173820108611/50000000000000000000)
  directionLo := (251061228751830231951/50000000000000000000)
  directionHi := (502122457503660463903/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree103.table
  base := (3223105785299329387321149765558317281719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-137948241564187824008506922670245000000000000)
      constant := (4110526710134067411022282066636954862376992398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree103.table
  base := (6446211557511824539623546670816235188957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-560458749253462626212334011350445000000000000)
      constant := (16771995146605207426280633614959602991689371237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251061228751830231951/50000000000000000000)
  centralHi := (502122457503660463903/100000000000000000000)
  directionLo := (504577838686490634181/100000000000000000000)
  directionHi := (252288919343245317091/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree104.table
  base := (13505140815945215112274543079501582412457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-278473673286883632682076063534470000000000000)
      constant := (8378514271938058450968285039019372034289071897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree104.table
  base := (13505140793892272090193653561788597353877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1131389955924700991073961205139670000000000000)
      constant := (34186467179210248307780045892067908447815572957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504577838686490634181/100000000000000000000)
  centralHi := (252288919343245317091/50000000000000000000)
  directionLo := (101404265838779192937/20000000000000000000)
  directionHi := (253510664596947982343/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree105.table
  base := (226051078466533509637047053680962317207/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-562101726890783234694276563456900000000000000)
      constant := (17074951761966718365598101384170862814324580875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree105.table
  base := (1766024048197385672375440939695313565237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-570931206671238364861627193789225000000000000)
      constant := (17417533601816126257857876872076360167775034868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101404265838779192937/20000000000000000000)
  centralHi := (253510664596947982343/50000000000000000000)
  directionLo := (254726550059843524553/50000000000000000000)
  directionHi := (509453100119687049107/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree106.table
  base := (14761577901663303794063635758942331907837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-283628053603899602012200499922430000000000000)
      constant := (8697938247370979504450663988306122211041976877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree106.table
  base := (29523155772023975786919553476545171310493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2304669741520504936745095140034460000000000000)
      constant := (70979580732691906573108615721269063833959506213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254726550059843524553/50000000000000000000)
  centralHi := (509453100119687049107/100000000000000000000)
  directionLo := (127968329623381506313/25000000000000000000)
  directionHi := (511873318493526025253/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree107.table
  base := (30810594609137196118840408117541619587927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-572410487524815173354525436232820000000000000)
      constant := (17719802742140189762066406705594567168755969767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree107.table
  base := (30810594582769954592588983876448540014293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2325614656356056414043681504912020000000000000)
      constant := (72301273334458804998814614320180807670597962013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127968329623381506313/25000000000000000000)
  centralHi := (511873318493526025253/100000000000000000000)
  directionLo := (514282147414811190371/100000000000000000000)
  directionHi := (128570536853702797593/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree108.table
  base := (1284748048738121816512930118808218573503/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-577564867841831142684649872620780000000000000)
      constant := (18046730504103623691323593078851317483017931575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree108.table
  base := (32118701196244984662677128262890193196903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2346559571191607891342267869789580000000000000)
      constant := (73635212212336071192131674443001584680221969023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514282147414811190371/100000000000000000000)
  centralHi := (128570536853702797593/25000000000000000000)
  directionLo := (258339873090471868561/50000000000000000000)
  directionHi := (516679746180943737123/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree109.table
  base := (33447475624402208004779126717156399683821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-582719248158847112014774309008740000000000000)
      constant := (18376659780577828100800272099182075841895546141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree109.table
  base := (8361868901424714831366407919778226033143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-591876121506789842160213558666785000000000000)
      constant := (18745349341526855445272817069640484140327934863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258339873090471868561/50000000000000000000)
  centralHi := (516679746180943737123/100000000000000000000)
  directionLo := (12976656760256551637/2500000000000000000)
  directionHi := (519066270410262065481/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree110.table
  base := (34796917820482204284750665198467236955523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-587873628475863081344898745396700000000000000)
      constant := (18709590571511296849505971485076058983924697683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree110.table
  base := (17398458902365902316387756236874808356517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1194224700431355422969720299772350000000000000)
      constant := (38169914397783900804309896537885205734551161197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12976656760256551637/2500000000000000000)
  centralHi := (519066270410262065481/100000000000000000000)
  directionLo := (260720936079956070449/50000000000000000000)
  directionHi := (521441872159912140899/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree111.table
  base := (3616702780051449964780071158455004768501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-296514004396439525337511590892330000000000000)
      constant := (9522761438427544882417492008643050463856482105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree111.table
  base := (36167027787251922543991385852889063272387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2409394315698262323238026964422260000000000000)
      constant := (77710506500522020169597891290445298476310551867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260720936079956070449/50000000000000000000)
  centralHi := (521441872159912140899/100000000000000000000)
  directionLo := (52380670003890653957/10000000000000000000)
  directionHi := (523806700038906539571/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree112.table
  base := (9389451389651517259244238190741908437871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-149545597277473755001286904543155000000000000)
      constant := (4846114174140632048827797605912146656736376191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree112.table
  base := (9389451386859815284251202324597317016449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-607584807633453450134153332324955000000000000)
      constant := (19773357620195900096122321578965702634524042409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52380670003890653957/10000000000000000000)
  centralHi := (523806700038906539571/100000000000000000000)
  directionLo := (526160899316610059491/100000000000000000000)
  directionHi := (131540224829152514873/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree113.table
  base := (19484625544558446691089278220324144895849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-301668384713455494667636027280290000000000000)
      constant := (9863196015294468774940161005785047551720019929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree113.table
  base := (1948462553985771374359905303351625911329/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-612821036342341319458799923544345000000000000)
      constant := (20122150184043451241399075792873377229124462445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526160899316610059491/100000000000000000000)
  centralHi := (131540224829152514873/25000000000000000000)
  directionLo := (528504612026876000217/100000000000000000000)
  directionHi := (264252306013438000109/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree114.table
  base := (40401364386632422661491738249592454088521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-608491149743926958665396490948540000000000000)
      constant := (20071328878891429177818799695071701828835174841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree114.table
  base := (40401364378717838142635970342220738542753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2472229060204916755133786059054940000000000000)
      constant := (81896017266520811376535482723667774683648348873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528504612026876000217/100000000000000000000)
  centralHi := (264252306013438000109/50000000000000000000)
  directionLo := (530837977068044350843/100000000000000000000)
  directionHi := (132709494267011087711/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree115.table
  base := (2615884090371262446608796591272964772961/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-153411382515235731998880231834125000000000000)
      constant := (5104816810357178800363455584195892615866496324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree115.table
  base := (20927072719638925846228396160274775487323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1246586987520234116216186211966250000000000000)
      constant := (41657840035829505588930704066337364081389316243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530837977068044350843/100000000000000000000)
  centralHi := (132709494267011087711/25000000000000000000)
  directionLo := (533161130299001106829/100000000000000000000)
  directionHi := (53316113029900110683/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree116.table
  base := (43327594262009967014604717752676235482751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-618799910377958897325645363724460000000000000)
      constant := (20770207118160950964432628402108628461258870671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree116.table
  base := (21663797128201076352772827432273128747947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1257059444938009854865479394405030000000000000)
      constant := (42373794575714206774922863169256303318212969827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533161130299001106829/100000000000000000000)
  centralHi := (53316113029900110683/10000000000000000000)
  directionLo := (535474204631486699621/100000000000000000000)
  directionHi := (267737102315743349811/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree117.table
  base := (44821710829976705280830001949845296471543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-623954290694974866655769800112420000000000000)
      constant := (21124148509049600635515181704234444593351092103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree117.table
  base := (44821710825256860419561244854157733087631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2535063804711571187029545153687620000000000000)
      constant := (86191744505674136118982259327501787925860784871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535474204631486699621/100000000000000000000)
  centralHi := (267737102315743349811/50000000000000000000)
  directionLo := (21511093204753240453/4000000000000000000)
  directionHi := (268888665059415505663/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree118.table
  base := (2316824757256305672016006772167623371313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-157277167752997708996473559125095000000000000)
      constant := (5370272853514330560102133540709728723620851365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree118.table
  base := (46336495141153922415761234032362161844909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2556008719547122664328131518565180000000000000)
      constant := (87648146134245968997722084159959036027672729269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21511093204753240453/4000000000000000000)
  centralHi := (268888665059415505663/50000000000000000000)
  directionLo := (270035317020641303727/50000000000000000000)
  directionHi := (108014126808256521491/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree119.table
  base := (47871947202882156496097344516134180997977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-634263051329006805316018672888340000000000000)
      constant := (21841035833147869005901624832309178847684975817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree119.table
  base := (47871947199539425983339097977958770359783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2576953634382674141626717883442740000000000000)
      constant := (89116794036998000268898248986904656961097807103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270035317020641303727/50000000000000000000)
  centralHi := (108014126808256521491/20000000000000000000)
  directionLo := (271177120494045302823/50000000000000000000)
  directionHi := (542354240988090605647/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree120.table
  base := (49428066998796340501111780404344016233809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-639417431646022774646143109276300000000000000)
      constant := (22203981766286004411439871860586808952588001089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree120.table
  base := (12357016748995880086024493399278465879843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-649474637304556404731326062080075000000000000)
      constant := (22649422053447073270931637029487281325256049563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271177120494045302823/50000000000000000000)
  centralHi := (542354240988090605647/100000000000000000000)
  directionLo := (68078534117061120339/12500000000000000000)
  directionHi := (544628272936488962713/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree121.table
  base := (10200970905707688726125875759349745706137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-644571811963038743976267545664260000000000000)
      constant := (22569929213437428769949556724262526678691555885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree121.table
  base := (51004854526171693364364437120706012202413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2618843464053777096223890613197860000000000000)
      constant := (92090828664478606158931951382106021336977514933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68078534117061120339/12500000000000000000)
  centralHi := (544628272936488962713/100000000000000000000)
  directionLo := (546892849327724865491/100000000000000000000)
  directionHi := (136723212331931216373/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree122.table
  base := (2104092391515538911373209026214392059863/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-649726192280054713306391982052220000000000000)
      constant := (22938878174568715516083045384241424987654370575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree122.table
  base := (10520461957179437697212038206923041783877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2639788378889328573522476978075420000000000000)
      constant := (93596215388934150807637072048725425908986014785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546892849327724865491/100000000000000000000)
  centralHi := (136723212331931216373/25000000000000000000)
  directionLo := (549148087140265314997/100000000000000000000)
  directionHi := (274574043570132657499/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree123.table
  base := (54220432772729653296370962415912217841057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-654880572597070682636516418440180000000000000)
      constant := (23310828649647255677712192597335960677519012497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree123.table
  base := (10844086554210876549480075565064815184749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2660733293724880050821063342952980000000000000)
      constant := (95113848387023378764523361498216728716672713545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549148087140265314997/100000000000000000000)
  centralHi := (274574043570132657499/50000000000000000000)
  directionLo := (551394100960308863361/100000000000000000000)
  directionHi := (275697050480154431681/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree124.table
  base := (11171844695808458144329101713923393033179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-660034952914086651966640854828140000000000000)
      constant := (23685780638641209255137313099836015981079054295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree124.table
  base := (27929611738816488045342432603927508180849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1340839104280215764059824853915270000000000000)
      constant := (48321863829308898002721024896018481289622582809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551394100960308863361/100000000000000000000)
  centralHi := (275697050480154431681/50000000000000000000)
  directionLo := (553631003049722767021/100000000000000000000)
  directionHi := (276815501524861383511/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree125.table
  base := (28759340951449184944742717163093060939599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-332594666615551310648382645608050000000000000)
      constant := (12031867070759731220095771129686360135702563679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree125.table
  base := (3594917618857054164589537105688240782233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-675655780848995751354559018177025000000000000)
      constant := (24546463300897949636494140325757177691614110212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553631003049722767021/100000000000000000000)
  centralHi := (276815501524861383511/50000000000000000000)
  directionLo := (69482362926439940973/12500000000000000000)
  directionHi := (111171780682303905557/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree126.table
  base := (29599404020228389162310224090897884960083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-335171856774059295313444863802030000000000000)
      constant := (12222344579125794890479132048472142146768817443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree126.table
  base := (14799702009864901753305648924834406531123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-680892009557883620679205609396415000000000000)
      constant := (24935056255455631714546891452276689219663712043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69482362926439940973/12500000000000000000)
  centralHi := (111171780682303905557/20000000000000000000)
  directionLo := (17439934682905652447/3125000000000000000)
  directionHi := (111615581970596175661/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree127.table
  base := (60899601887959059441146535822885055948569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-675498093865134559957014163992020000000000000)
      constant := (24828645688807820542820532915172992528168615049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree127.table
  base := (60899601887120353976310827929185612470643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2744512953067085960015408802463220000000000000)
      constant := (101306843113189736091381850418778956209171872363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17439934682905652447/3125000000000000000)
  centralHi := (111615581970596175661/20000000000000000000)
  directionLo := (140072032011632926223/25000000000000000000)
  directionHi := (560288128046531704893/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree128.table
  base := (3913816465107851013298994832686509291629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-170163118545537632321784650094995000000000000)
      constant := (6303900933289752159433296644315319360395973236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree128.table
  base := (1956908232531882425765235528272117360449/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-691364466975659359328498791835195000000000000)
      constant := (25721426869393919934787719105231415298769171272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140072032011632926223/25000000000000000000)
  centralHi := (560288128046531704893/100000000000000000000)
  directionLo := (281244830794230582433/50000000000000000000)
  directionHi := (562489661588461164867/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree129.table
  base := (64363192698152298807991699737105592168407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-685806854499166498617263036767940000000000000)
      constant := (25605563291276605594880589670191893395565951847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree129.table
  base := (2574527707902363545203722159529662679283/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2786402782738188914612581532218340000000000000)
      constant := (104476818114865004776067100372727528047672665075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281244830794230582433/50000000000000000000)
  centralHi := (562489661588461164867/100000000000000000000)
  directionLo := (282341306027791663073/50000000000000000000)
  directionHi := (564682612055583326147/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree130.table
  base := (66125989653707320365777717243398366706893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-690961234816182467947387473155900000000000000)
      constant := (25998524363132636130536823248489958462685299453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree130.table
  base := (16531497413302117916162328548700141909083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-701836924393435097977791974273975000000000000)
      constant := (26520043756236164151442689148500151246908928403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282341306027791663073/50000000000000000000)
  centralHi := (564682612055583326147/100000000000000000000)
  directionLo := (283433539529962506673/50000000000000000000)
  directionHi := (566867079059925013347/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree131.table
  base := (13581890860985690804630787253381413067671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-696115615133198437277511909543860000000000000)
      constant := (26394486948699675945720159098208250864545109955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree131.table
  base := (679094543045089815867059163743329657679/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-707073153102322967302438565493365000000000000)
      constant := (26923944551925948107031158195374020639042320975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283433539529962506673/50000000000000000000)
  centralHi := (566867079059925013347/100000000000000000000)
  directionLo := (113808632060304833719/20000000000000000000)
  directionHi := (142260790075381042149/25000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree132.table
  base := (34856793324210235888453435874913750828291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-350634997725107203303818172965910000000000000)
      constant := (13396725523975415719708571602101951820310893011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree132.table
  base := (34856793324033882934976324571236652221557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1424618763622421673254170313425510000000000000)
      constant := (54661813831516850927666611726123753573830907837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113808632060304833719/20000000000000000000)
  centralHi := (142260790075381042149/25000000000000000000)
  directionLo := (285605475809708954661/50000000000000000000)
  directionHi := (571210951619417909323/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree133.table
  base := (71538386680852792011778183135484167430083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-706424375767230375937760782319780000000000000)
      constant := (27195416660859721074653314250927490090213687443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree133.table
  base := (71538386680556242549235895899112098997511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2870182442080394823806926991728580000000000000)
      constant := (110963723390827733792651041576770770763979249951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285605475809708954661/50000000000000000000)
  centralHi := (571210951619417909323/100000000000000000000)
  directionLo := (114674109408179114657/20000000000000000000)
  directionHi := (286685273520447786643/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree134.table
  base := (73383854398957307755598738479694262325859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-711578756084246345267885218707740000000000000)
      constant := (27600383787400458176102120544249138251883129139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree134.table
  base := (73383854398707987808224895919455438893737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2891127356915946301105513356606140000000000000)
      constant := (112616065390981228754579033250682751717594227217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114674109408179114657/20000000000000000000)
  centralHi := (286685273520447786643/50000000000000000000)
  directionLo := (575522038829088368227/100000000000000000000)
  directionHi := (143880509707272092057/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree135.table
  base := (37624994899763186048739586606280444229809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-358366568200631157299004827547850000000000000)
      constant := (14004176213773817486291203713705347398744317089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree135.table
  base := (18812497449829192846315679707071383016333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-728018067937874444601024930370925000000000000)
      constant := (28570163415847863979325862191957774183226325653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575522038829088368227/100000000000000000000)
  centralHi := (143880509707272092057/25000000000000000000)
  directionLo := (11553310350579275517/2000000000000000000)
  directionHi := (577665517528963775851/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree136.table
  base := (19284198219852730217047104813413846711627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-180471879179569570982033522870915000000000000)
      constant := (7104830645319076931702423902536771079802797467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree136.table
  base := (77136792879234721364518517959688972644441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2933017186587049255702686086361260000000000000)
      constant := (115957488207957554316769151970193274372500534081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11553310350579275517/2000000000000000000)
  centralHi := (577665517528963775851/100000000000000000000)
  directionLo := (1449502680029473961/250000000000000000)
  directionHi := (579801072011789584401/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree137.table
  base := (79044263635518715749548980164433964581531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-727041897035294253258258527871620000000000000)
      constant := (28833294248561982819065701143168601433450307051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree137.table
  base := (79044263635370602757316030108380988922263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-2953962101422600733001272451238820000000000000)
      constant := (117646569024580477692703966708408755266058228783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1449502680029473961/250000000000000000)
  centralHi := (579801072011789584401/100000000000000000000)
  directionLo := (581928789518129329089/100000000000000000000)
  directionHi := (58192878951812932909/10000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree138.table
  base := (80972402064812693549913471164575980942311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-732196277352310222588382964259580000000000000)
      constant := (29250267429380603671809385091630326345044045431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree138.table
  base := (1619448041293763933094209216191718737591/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1487453508129076105149929408058190000000000000)
      constant := (59673948056581471277523196411515831501778830775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581928789518129329089/100000000000000000000)
  centralHi := (58192878951812932909/10000000000000000000)
  directionLo := (116809751139885598727/20000000000000000000)
  directionHi := (146012188924856998409/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree139.table
  base := (10365151020538676192160863938423812933137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-184337664417331547979626850161885000000000000)
      constant := (7417560530927134604829653803259430044486756354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree139.table
  base := (41460604082102384361581428107283626628797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1497925965546851843799222590496970000000000000)
      constant := (60530734736804689556507754346897314680813284677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116809751139885598727/20000000000000000000)
  centralHi := (146012188924856998409/25000000000000000000)
  directionLo := (146540263664561014747/25000000000000000000)
  directionHi := (586161054658244058989/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree140.table
  base := (1697813638621551290573504123947524187607/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-371252518993171080624315918517750000000000000)
      constant := (15046609165761284120382447640465708477250876175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree140.table
  base := (84890681930989617484050018459342948839317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3016796845929255164897031545871500000000000000)
      constant := (122787289105825884760534748437937807423760555997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146540263664561014747/25000000000000000000)
  centralHi := (586161054658244058989/100000000000000000000)
  directionLo := (294132884493590683589/50000000000000000000)
  directionHi := (588265768987181367179/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree141.table
  base := (347523293448946427803094472676369818773/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-373829709151679065289378136711730000000000000)
      constant := (15259598026399938143568039236508030666812616625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree141.table
  base := (43440411681081347108881325676616714918361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1518870880382403321097808955374530000000000000)
      constant := (62262677504860089928289555298107816162699204801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294132884493590683589/50000000000000000000)
  centralHi := (588265768987181367179/100000000000000000000)
  directionLo := (59036297980657179007/10000000000000000000)
  directionHi := (590362979806571790071/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree142.table
  base := (8889163245495540236076274603112081625401/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-376406899310187049954440354905710000000000000)
      constant := (15474087643759018571255296155435113992774006605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree142.table
  base := (1777832649097865750170375104171666643803/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1529343337800179059747102137813310000000000000)
      constant := (63137833592600782788337762058317969273352298075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59036297980657179007/10000000000000000000)
  centralHi := (590362979806571790071/100000000000000000000)
  directionLo := (296226383400478673139/50000000000000000000)
  directionHi := (592452766800957346279/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree143.table
  base := (45461554603225481993258982137535862936991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-378984089468695034619502573099690000000000000)
      constant := (15690078017827503384333218817920981570323905711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree143.table
  base := (90923109206398766433672031388468430433879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3079631590435909596792790640504180000000000000)
      constant := (128038225632180883643431478944573036979531917039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296226383400478673139/50000000000000000000)
  centralHi := (592452766800957346279/100000000000000000000)
  directionLo := (297267604127209093327/50000000000000000000)
  directionHi := (118907041650883637331/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree144.table
  base := (9297525361398723874617174116932064869977/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-381561279627203019284564791293670000000000000)
      constant := (15907569148594556444571070864542534429175439085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree144.table
  base := (92975253613943377232033150479798561458629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3100576505271461074091377005381740000000000000)
      constant := (129813030350570477770584707776302105707695931789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297267604127209093327/50000000000000000000)
  centralHi := (118907041650883637331/20000000000000000000)
  directionLo := (298305190542395381177/50000000000000000000)
  directionHi := (119322076216958152471/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree145.table
  base := (47524032837436971982721744495398852089237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-384138469785711003949627009487650000000000000)
      constant := (16126561036049522887437364027622554307398846277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree145.table
  base := (47524032837418544492631230370521629942761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1560760710053506275694981685129650000000000000)
      constant := (65800040670142078338740344915186383544996005201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298305190542395381177/50000000000000000000)
  centralHi := (119322076216958152471/20000000000000000000)
  directionLo := (299339180438409246273/50000000000000000000)
  directionHi := (598678360876818492547/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree146.table
  base := (48570772693232725325321507331126530373427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-386715659944218988614689227681630000000000000)
      constant := (16347053680181924699302588297478593247087915267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree146.table
  base := (24285386346608621109049228567412494776047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-785616583735641007172137433784215000000000000)
      constant := (33349844650309289637445665972234833745119321927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299339180438409246273/50000000000000000000)
  centralHi := (598678360876818492547/100000000000000000000)
  directionLo := (600739221914275355071/100000000000000000000)
  directionHi := (9386550342410552423/1562500000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree147.table
  base := (49627846373079854857565406832661562042001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-389292850102726973279751445875610000000000000)
      constant := (16569047080981456464759107916465672232934689921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree147.table
  base := (12406961593266711570745583198545375917341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-790852812444528876496784025003605000000000000)
      constant := (33802730533336529209543739287766264779535045962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600739221914275355071/100000000000000000000)
  centralHi := (9386550342410552423/1562500000000000000)
  directionLo := (301396518605550513321/50000000000000000000)
  directionHi := (602793037211101026643/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree148.table
  base := (101390507751397218013455893632994604429903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-783740080522469915889627328139180000000000000)
      constant := (33585082476875962543198728458628470261689261663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree148.table
  base := (20278101550275071994574279621869433103393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3184356164613666983285722464891980000000000000)
      constant := (137034711936529027300313882018959112530329075565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301396518605550513321/50000000000000000000)
  centralHi := (602793037211101026643/100000000000000000000)
  directionLo := (604839878541584494073/100000000000000000000)
  directionHi := (302419939270792247037/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree149.table
  base := (51772995199830010711960053657472550599131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-394447230419742942609875882263570000000000000)
      constant := (17017536152541526762524371723839380073295716651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree149.table
  base := (20709198079928331690562596225035519368399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3205301079449218460584308829769540000000000000)
      constant := (138870748010705216202711738040624895380414361795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604839878541584494073/100000000000000000000)
  centralHi := (302419939270792247037/50000000000000000000)
  directionLo := (606879816469631439087/100000000000000000000)
  directionHi := (37929988529351964943/6250000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree150.table
  base := (21144428137694150509645867716812277667513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-794048841156501854549876200915100000000000000)
      constant := (34488063646564562647906373106239350257021852365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree150.table
  base := (105722140688455326483802108412762741552367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3226245994284769937882895194647100000000000000)
      constant := (140719030355795309608942529937368331002079391047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606879816469631439087/100000000000000000000)
  centralHi := (37929988529351964943/6250000000000000000)
  directionLo := (3805705752357182261/625000000000000000)
  directionHi := (608912920377149161761/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree151.table
  base := (26979739653847925218910535951286716953411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-199800805368379455970000159325765000000000000)
      constant := (8736014125325295201704008614818962084987968531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree151.table
  base := (10791895861537874257481414181502969918721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1623595454560160707590740779762330000000000000)
      constant := (71289779485860601844406168638999323295828697805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/625000000000000000)
  centralHi := (608912920377149161761/100000000000000000000)
  directionLo := (305469629245790673429/50000000000000000000)
  directionHi := (610939258491581346859/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree152.table
  base := (55068222089011956748253904778447502787547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-402178800895266896605062536845510000000000000)
      constant := (17701525434636952947890192102889042669580159787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree152.table
  base := (110136444178013028658832597699878683100877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3268135823955872892480067924402220000000000000)
      constant := (144452333858406035990175884910459732885235199957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305469629245790673429/50000000000000000000)
  centralHi := (610939258491581346859/100000000000000000000)
  directionLo := (61295889791262358899/10000000000000000000)
  directionHi := (612958897912623588991/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree153.table
  base := (112374597374006324652906615128460439354399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-809511982107549762540249510078980000000000000)
      constant := (35865046750464035912930940237995455140126194479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree153.table
  base := (28093649343499295474448424073828029276337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-822270184697856092444663572319945000000000000)
      constant := (36584338753943539405274692816769253886043113817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61295889791262358899/10000000000000000000)
  centralHi := (612958897912623588991/100000000000000000000)
  directionLo := (122994380927629854511/20000000000000000000)
  directionHi := (153742976159537318139/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree154.table
  base := (11463341820101491258778841673978243236479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-407333181212282865935186973233470000000000000)
      constant := (18165022072426581140965054183523048323380750795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree154.table
  base := (114633418201007233428174678129106127806309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3310025653626975847077240654157340000000000000)
      constant := (148234622443751106295224863611600969441041946669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122994380927629854511/20000000000000000000)
  centralHi := (153742976159537318139/25000000000000000000)
  directionLo := (77122292948671768389/12500000000000000000)
  directionHi := (616978343589374147113/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree155.table
  base := (29228226664190470575793312413002900019533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-204955185685395425300124595713725000000000000)
      constant := (9199510763105790844649722323058395971054720893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree155.table
  base := (116912906656755432714492422557003805677739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3330970568462527324375827019034900000000000000)
      constant := (150144136142263580197646747275468958937720435299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77122292948671768389/12500000000000000000)
  centralHi := (616978343589374147113/100000000000000000000)
  directionLo := (1237956557270573489/200000000000000000)
  directionHi := (618978278635286744501/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree156.table
  base := (14901632842374359120812197563223789703059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-206243780764649417632655704810715000000000000)
      constant := (9317260868289049563195636816454611276475860678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree156.table
  base := (59606531369494728148766051691757625288389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1675957741649039400837206691956230000000000000)
      constant := (76032948055619706316203860006275646071865271949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1237956557270573489/200000000000000000)
  centralHi := (618978278635286744501/100000000000000000000)
  directionLo := (620971772616370647427/100000000000000000000)
  directionHi := (155242943154092661857/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree157.table
  base := (97227109156396951052239489404315855371/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-415064751687806819930373627815410000000000000)
      constant := (18871522703517350268173310204595501181496056875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree157.table
  base := (30383471611372909956920813725457743714707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-843215099533407569743249937197505000000000000)
      constant := (38499975587651886854020478222784021566362926987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620971772616370647427/100000000000000000000)
  centralHi := (155242943154092661857/25000000000000000000)
  directionLo := (1557397218419108843/250000000000000000)
  directionHi := (622958887367643537201/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree158.table
  base := (2477507555481641050136912490669626581239/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-417641941846314804595435846009390000000000000)
      constant := (19110024427020686264479660437976512803749852975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree158.table
  base := (61937688887039116181905734515946073501139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1696902656484590878135793056833790000000000000)
      constant := (77973077430149007492382219170965088141049994699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1557397218419108843/250000000000000000)
  centralHi := (622958887367643537201/100000000000000000000)
  directionLo := (124987936748207383567/20000000000000000000)
  directionHi := (156234920935259229459/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree159.table
  base := (63118768361300939971644710722759513276791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-420219132004822789260498064203370000000000000)
      constant := (19350026907079589726990801497896218104665461511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree159.table
  base := (15779692090324833999590209844259043552841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-853687556951183308392543119636285000000000000)
      constant := (39476163410060477296080694305639428028953156962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124987936748207383567/20000000000000000000)
  centralHi := (156234920935259229459/25000000000000000000)
  directionLo := (31345711081356971609/5000000000000000000)
  directionHi := (626914221627139432181/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree160.table
  base := (128620363288937575676401573963968119671293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-845592644326661547851120564794700000000000000)
      constant := (39183060287371343877368043445592591475916311853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree160.table
  base := (128620363288934881925218425046951257613661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3435695142640284710868758843422700000000000000)
      constant := (159875398690371364715969825830513365245199312101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31345711081356971609/5000000000000000000)
  centralHi := (626914221627139432181/100000000000000000000)
  directionLo := (157220639994081437583/25000000000000000000)
  directionHi := (628882559976325750333/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree161.table
  base := (13102385747100284806045457789901724261481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-425373512321838758590622500591330000000000000)
      constant := (19834534136830670141496417332332997789375955005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree161.table
  base := (65511928735500293086751978249693699700717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (673398)
      previous := (0)
      next := (544160)
      square := (9467524635261905142542826548190000000000000)
      linear := (-1728320028737918094083672604150130000000000000)
      constant := (80929195005309767605582524206416375832110673397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/25000000000000000000)
  centralHi := (628882559976325750333/100000000000000000000)
  directionLo := (630844756819292119011/100000000000000000000)
  directionHi := (157711189204823029753/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree162.table
  base := (133448019266742543378777863350240226907713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-855901404960693486511369437570620000000000000)
      constant := (40158077773012889798266229068831372837335994673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree162.table
  base := (3336200481668516104810018750764448939257/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-869396243077846916366482893294455000000000000)
      constant := (40963406900230142977893061988120967084627335370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630844756819292119011/100000000000000000000)
  centralHi := (157711189204823029753/25000000000000000000)
  directionLo := (25312034771480752419/4000000000000000000)
  directionHi := (158200217321754702619/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree163.table
  base := (108714278939305598575987553133468861547/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-430527892638854727920746936979290000000000000)
      constant := (20325044392704977532153315159502739282696116875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree163.table
  base := (135892848674130403634675390572864652333003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3498529887146939142764517938055380000000000000)
      constant := (165861111461209602931333718597283876325401749123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25312034771480752419/4000000000000000000)
  centralHi := (158200217321754702619/25000000000000000000)
  directionLo := (126950190726035779741/20000000000000000000)
  directionHi := (317375476815089449353/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree164.table
  base := (138358345691176409424827957881483296305681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-866210165594725425171618310346540000000000000)
      constant := (41145101310836735245289648043432909190037299201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree164.table
  base := (34589586422793767659358762677873091710397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-879868700495622655015776075733235000000000000)
      constant := (41970210397855678270072127816009151731492830277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126950190726035779741/20000000000000000000)
  centralHi := (317375476815089449353/50000000000000000000)
  directionLo := (12733901304760240341/2000000000000000000)
  directionHi := (636695065238012017051/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree165.table
  base := (17605563789488777620610794410045564940579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-217841136477935348625435686683625000000000000)
      constant := (10410778837319415292978537781235691839788652518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree165.table
  base := (140844510315909096982898863461285349061273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3540419716818042097361690667810500000000000000)
      constant := (169912817991496924227990709193670043869272248193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12733901304760240341/2000000000000000000)
  centralHi := (636695065238012017051/100000000000000000000)
  directionLo := (127726651731336202651/20000000000000000000)
  directionHi := (79829157332085126657/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree166.table
  base := (2867026850927930543008956122575940875343/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (165718)
      previous := (0)
      next := (135280)
      square := (2340509429665414644801402237390000000000000)
      linear := (-438259463114378681915933591561230000000000000)
      constant := (21072065450358695307105966089014440691839797575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree166.table
  base := (35837835636598895885855429740049555083059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-890341157913398393665069258172015000000000000)
      constant := (42989260165342544047372858855273597794416293419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127726651731336202651/20000000000000000000)
  centralHi := (79829157332085126657/12500000000000000000)
  directionLo := (160141396901782178269/25000000000000000000)
  directionHi := (640565587607128713077/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree167.table
  base := (145878842380726491597663470518903722877681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-881673306545773333161991619510420000000000000)
      constant := (42648147965140803679186524541780956388914111201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree167.table
  base := (29175768476145139889597373494750836709927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3582309546489145051958863397565620000000000000)
      constant := (174013509600981308114852442268067277795113855035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160141396901782178269/25000000000000000000)
  centralHi := (640565587607128713077/100000000000000000000)
  directionLo := (321246052501225665367/50000000000000000000)
  directionHi := (128498421000490266147/20000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree168.table
  base := (37106752454254695353675627614862600157391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19802500000000000000000000000000000000000000
      center := (82859)
      previous := (0)
      next := (67640)
      square := (1170254714832707322400701118695000000000000)
      linear := (-221706921715697325623029013974595000000000000)
      constant := (10788791635633249582250434037117606655846694111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree168.table
  base := (148427009817018116435918542026695783872597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1346796)
      previous := (0)
      next := (1088320)
      square := (18935049270523810285085653096380000000000000)
      linear := (-3603254461324696529257449762443180000000000000)
      constant := (176082224810270040365273417484934479611061880477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell216.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321246052501225665367/50000000000000000000)
  centralHi := (128498421000490266147/20000000000000000000)
  directionLo := (128882572592960884341/20000000000000000000)
  directionHi := (322206431482402210853/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree169.table
  base := (150995844853419016093700910326683991738611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (331436)
      previous := (0)
      next := (270560)
      square := (4681018859330829289602804474780000000000000)
      linear := (-891982067179805271822240492286340000000000000)
      constant := (43665186632879286015654776130341543898561537731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree169.table
  base := (4718620151669326809052063156972247432471/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (336699)
      previous := (0)
      next := (272080)
      square := (4733762317630952571271413274095000000000000)
      linear := (-906049844040062001639009031830185000000000000)
      constant := (44540796572294239214887854600260352239870426488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell216.Kernel169
