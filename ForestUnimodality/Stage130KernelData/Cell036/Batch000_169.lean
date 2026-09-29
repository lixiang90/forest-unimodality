import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell036.Parameters
import ForestUnimodality.BinomialMassData.Q869_1824.Batch000_049
import ForestUnimodality.BinomialMassData.Q869_1824.Batch050_099
import ForestUnimodality.BinomialMassData.Q869_1824.Batch100_149
import ForestUnimodality.BinomialMassData.Q869_1824.Batch150_199
import ForestUnimodality.BinomialMassData.Q581_1216.Batch000_049
import ForestUnimodality.BinomialMassData.Q581_1216.Batch050_099
import ForestUnimodality.BinomialMassData.Q581_1216.Batch100_149
import ForestUnimodality.BinomialMassData.Q581_1216.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree000.table
  base := (34964734111101963798802217/500000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (75069986297282800813412962000000000000)
      linear := (4528208492847313887397220400000000000)
      constant := (69929468222203927597604434000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree000.table
  base := (34964734111101963798802217/500000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (75069986297282800813412962000000000000)
      linear := (4528208492847313887397220400000000000)
      constant := (69929468222203927597604434000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree001.table
  base := (414495615637386305123934864756172112077153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-2176904525606958879730204463420250000000000)
      constant := (1347179775341428689187351440604702992919920097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree001.table
  base := (206839790233040523560564462424686933231559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-121310580347864479398758280852687500000000)
      constant := (74696192519314560674862288887267504869249049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6243049135521542601/12500000000000000000)
  directionHi := (49944393084172340809/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree002.table
  base := (51225709956676308425757820360943637856119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-900186109029305397532388923527300000000000)
      constant := (166847184726599318896884866176984870019530631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree002.table
  base := (25522482703837979684786709712342474141683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-50158915405063672072853708905475000000000)
      constant := (9236800942658572923619409627594913243272563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6243049135521542601/12500000000000000000)
  centralHi := (49944393084172340809/100000000000000000000)
  directionLo := (70632038064129537691/100000000000000000000)
  directionHi := (17658009516032384423/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree003.table
  base := (165980597302858600450319622527538939792159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-758328507187343899510409419094750000000000)
      constant := (60449244043408414851999208435606608046219399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree003.table
  base := (3304273439406058421573799303999731440817/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-76055714740554448265955761640412500000000)
      constant := (6017550670734963221475819236864042301455935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70632038064129537691/100000000000000000000)
  centralHi := (17658009516032384423/25000000000000000000)
  directionLo := (21626556593744538247/25000000000000000000)
  directionHi := (86506226374978152989/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree004.table
  base := (113027316171672361852177911024921429154697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-9148982584225663203525424926069000000000000)
      constant := (375803181478018617588160747553141035823610553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree004.table
  base := (22486407547447861686957891132975268355307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-203905028152090448918115628750700000000000)
      constant := (8309318978907243815533430310017762501265827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21626556593744538247/25000000000000000000)
  centralHi := (86506226374978152989/100000000000000000000)
  directionLo := (6243049135521542601/6250000000000000000)
  directionHi := (99888786168344681617/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree005.table
  base := (20167940713314621568444256306189994432557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-5736504301882615655728582540142625000000000)
      constant := (137796204672363852694040485495348843588380386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree005.table
  base := (80222783923929976486977059156160414206021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-1278493134115360006521598671102875000000000)
      constant := (30468046298236997167983921940636258161186081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6243049135521542601/6250000000000000000)
  centralHi := (99888786168344681617/100000000000000000000)
  directionLo := (111679058031179729887/100000000000000000000)
  directionHi := (3489970563474366559/3125000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree006.table
  base := (29976099313473829928775236098021747785079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-766501923516933301077161401916750000000000)
      constant := (11905232827074910908028889483348577512913519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree006.table
  base := (5961319555705503829552019764472562312797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-153746112747026776845261919845225000000000)
      constant := (2370071081308348730046504287177290698044717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111679058031179729887/100000000000000000000)
  centralHi := (3489970563474366559/3125000000000000000)
  directionLo := (122338278569211246161/100000000000000000000)
  directionHi := (61169139284605623081/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree007.table
  base := (22998969310533833733372312251762643723493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-8060530321422183763660322694358875000000000)
      constant := (88041835478908831739082665572377323598253757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree007.table
  base := (45737597214316362740505060759880640631317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-1796429120825175530383639725801625000000000)
      constant := (19488079611626064140821628799679189588217937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122338278569211246161/100000000000000000000)
  centralHi := (61169139284605623081/50000000000000000000)
  directionLo := (26428088696554848377/20000000000000000000)
  directionHi := (66070221741387120943/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree008.table
  base := (36120819432221870855952937200821578932223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-18445086662383935635252385542934000000000000)
      constant := (152227006658499829129691067793337559950792527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree008.table
  base := (35916059929539458985093797059373920563889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-2055397114180083292314660253151000000000000)
      constant := (16862698337075736496955215353702297823563929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26428088696554848377/20000000000000000000)
  centralHi := (66070221741387120943/50000000000000000000)
  directionLo := (141264076128259075383/100000000000000000000)
  directionHi := (17658009516032384423/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree009.table
  base := (7201831595935259337230938297143048858637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-1153839593440194652399118094286125000000000)
      constant := (7655932711383142018553088151677884791560914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree009.table
  base := (14321149370205130735756240350908145345391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-1157182553767495527122840390250187500000000)
      constant := (7640399059018563351254707652550370254842401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141264076128259075383/100000000000000000000)
  centralHi := (17658009516032384423/12500000000000000000)
  directionLo := (5993327170100680897/4000000000000000000)
  directionHi := (74916589626258511213/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree010.table
  base := (2897798043677855824730608966686227910073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-11546569350731535925557932925683250000000000)
      constant := (64989949155988253140458523886448631981808708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree010.table
  base := (576163508888446944234827107435361661521/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-257333310088989881617670130784975000000000)
      constant := (1442839079631812259012137076615914192361324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5993327170100680897/4000000000000000000)
  centralHi := (74916589626258511213/50000000000000000000)
  directionLo := (19742254812593287059/12500000000000000000)
  directionHi := (157938038500746296473/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree011.table
  base := (18722616121801746678990134745354229803773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-25417164721002639959047606005582750000000000)
      constant := (127045882632684100770389163286298037163708477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree011.table
  base := (18608975757818010610667310351836658505487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-2832301094244806578107721835199125000000000)
      constant := (14117825316744072846018426341423726103293307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19742254812593287059/12500000000000000000)
  centralHi := (157938038500746296473/100000000000000000000)
  directionLo := (165646812242220771923/100000000000000000000)
  directionHi := (41411703060555192981/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree012.table
  base := (7551047654786021269536598808680028985687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-1541177263363456003721074786655500000000000)
      constant := (7108100384537063143013588869049646713833007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree012.table
  base := (600238732845070437980006496639775855751/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-618253817519942868007748472509700000000000)
      constant := (2846453771456849982930829662554711044630555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165646812242220771923/100000000000000000000)
  centralHi := (41411703060555192981/25000000000000000000)
  directionLo := (173012452749956305977/100000000000000000000)
  directionHi := (86506226374978152989/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree013.table
  base := (12108632201146680872421894474475450520539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-30065216760081776174911086314015250000000000)
      constant := (131990266805979277502354489914705570772481211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree013.table
  base := (12026761027187764715264828536958066432653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-3350237080954622101969762889897875000000000)
      constant := (14695638134340886366532257565201038740000233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173012452749956305977/100000000000000000000)
  centralHi := (86506226374978152989/50000000000000000000)
  directionLo := (180077070186912429363/100000000000000000000)
  directionHi := (45019267546728107341/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree014.table
  base := (4798874741925550929662634988175017832057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-16194621389810672141421413234115750000000000)
      constant := (69354927748370439350238970100467734498853193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree014.table
  base := (1905553301579308005052110885234085605539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-721841014861905972780156683449450000000000)
      constant := (3091219621605652848399556360107402559849579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180077070186912429363/100000000000000000000)
  centralHi := (45019267546728107341/25000000000000000000)
  directionLo := (46718701827833697867/25000000000000000000)
  directionHi := (186874807311334791469/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree015.table
  base := (1493382686060069132950081535678998570463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-771405973314686942017212591609950000000000)
      constant := (3283809798081737903657622332735872390187143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree015.table
  base := (3703505031604059722485036464581666309827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-1934086533832218812915901972298312500000000)
      constant := (8238417955815075148594993788009237885503797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46718701827833697867/25000000000000000000)
  centralHi := (186874807311334791469/100000000000000000000)
  directionLo := (19343380265143636259/10000000000000000000)
  directionHi := (193433802651436362591/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree016.table
  base := (1410185929589075276448479271213915305363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-18518647409350240249353153388332000000000000)
      constant := (79465056195082267580723284255267521654248774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree016.table
  base := (1397368429753781121494027237007622154261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-2063570530509672693881412235973000000000000)
      constant := (8865385028246890448895119290650628195376442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19343380265143636259/10000000000000000000)
  centralHi := (193433802651436362591/100000000000000000000)
  directionLo := (199777572336689363233/100000000000000000000)
  directionHi := (99888786168344681617/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree017.table
  base := (162489908966280911896183018662529445233/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-7872264167648009721327609386176050000000000)
      constant := (34400140178254481327001441633225675994060085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree017.table
  base := (2009205988262053303762414955049734715161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-2193054527187126574846922499647687500000000)
      constant := (9598707708777360560293200628825304329829371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199777572336689363233/100000000000000000000)
  centralHi := (99888786168344681617/50000000000000000000)
  directionLo := (205926008093410758149/100000000000000000000)
  directionHi := (4118520161868215163/2000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree018.table
  base := (2687419097471842323510490462495671698807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-4631705206419957412729976342788500000000000)
      constant := (20760025531678042044606371739881515608269327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree018.table
  base := (1324999081653385993658545523291552482833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-2322538523864580455812432763322375000000000)
      constant := (10430475283033178447864242171767182086927713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205926008093410758149/100000000000000000000)
  centralHi := (4118520161868215163/2000000000000000000)
  directionLo := (105948057096194306537/50000000000000000000)
  directionHi := (8475844567695544523/4000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree019.table
  base := (1481760579829720825636256094940530337591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1260)
      previous := (630)
      next := (630)
      square := (6756298766755452073207166580000000000000)
      linear := (-121909620158778905325488995122750000000000)
      constant := (563259328196349155705291930657515554288319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree019.table
  base := (1449874481428410823717709016432130200647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (140)
      previous := (70)
      next := (70)
      square := (750699862972828008134129620000000000000)
      linear := (-13584612302171935383811318709125000000000)
      constant := (62905740545635063669878633387351075513147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105948057096194306537/50000000000000000000)
  centralHi := (8475844567695544523/4000000000000000000)
  directionLo := (108851281125189469401/50000000000000000000)
  directionHi := (217702562250378938803/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree020.table
  base := (417942269320083242938497178715278546563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-46333398896858752930433267393529000000000000)
      constant := (221401069121303948686786206114758752497783187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree020.table
  base := (195412707038339900540231458082332208909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-2581506517219488217743453290671750000000000)
      constant := (12365827964354584225465611219695885989916149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108851281125189469401/50000000000000000000)
  centralHi := (217702562250378938803/100000000000000000000)
  directionLo := (8934324642494378391/4000000000000000000)
  directionHi := (3489970563474366559/1562500000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree021.table
  base := (-525844056352818507656699528993836889101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-5406380546266480115373889727527250000000000)
      constant := (26773636644236578145675295441690963164284539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree021.table
  base := (-13721492338812161099677215665721805291/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-542198102779388419741792710869287500000000)
      constant := (2692116379488682069785892036776860701441046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8934324642494378391/4000000000000000000)
  centralHi := (3489970563474366559/1562500000000000000)
  directionLo := (22887396184684871411/10000000000000000000)
  directionHi := (228873961846848714111/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree022.table
  base := (-683542513851113367588385539105796681689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-25490725467968944573148373850980750000000000)
      constant := (130982392723410142410227301286606180643692439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree022.table
  base := (-693291129250634552533103973079723057203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-2840474510574395979674473818021125000000000)
      constant := (14635607011977493657363222367657042241974717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22887396184684871411/10000000000000000000)
  centralHi := (228873961846848714111/100000000000000000000)
  directionLo := (234259968436818250149/100000000000000000000)
  directionHi := (4685199368736365003/2000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree023.table
  base := (-2119847346511914511252956319628007250619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-53305476955477457254228487856177750000000000)
      constant := (284361533353281714505187141882847967723988869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree023.table
  base := (-267041709625426702327185486321378570627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-2969958507251849860639984081695812500000000)
      constant := (15888377860936643099485761483924115379170862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234259968436818250149/100000000000000000000)
  centralHi := (4685199368736365003/2000000000000000000)
  directionLo := (59881223691448873031/25000000000000000000)
  directionHi := (1916199158126363937/800000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree024.table
  base := (-21839615487388184623455652809565143867/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-3090527943056501409008901556133000000000000)
      constant := (17117562811448373740796706776482931916096832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree024.table
  base := (-140469345153135557857102556538563016463/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-619888500785860748321098869074100000000000)
      constant := (3443371935224634873732124544917338752113714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59881223691448873031/25000000000000000000)
  centralHi := (1916199158126363937/800000000000000000)
  directionLo := (244676557138422492323/100000000000000000000)
  directionHi := (61169139284605623081/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree025.table
  base := (-1701554821787374368330915005415880535359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-28976764497278296735045984082305125000000000)
      constant := (166599417428839582965542534435454048281243609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree025.table
  base := (-3414836998314438694564236604997563527481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-6457853001213515245142009218090375000000000)
      constant := (37238821597823839942188930154585845386891859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244676557138422492323/100000000000000000000)
  centralHi := (61169139284605623081/25000000000000000000)
  directionLo := (249721965420861704041/100000000000000000000)
  directionHi := (124860982710430852021/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree026.table
  base := (-1975080389000622159233983152504456169029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-30138777507048080789011854159413250000000000)
      constant := (179792806874603988170422112251455060969324779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree026.table
  base := (-247501777310310128504307071215903986741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-3358410497284211503536514872719875000000000)
      constant := (20094705551708630875341418996912885301916992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249721965420861704041/100000000000000000000)
  centralHi := (124860982710430852021/50000000000000000000)
  directionLo := (127333717465371647901/50000000000000000000)
  directionHi := (254667434930743295803/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree027.table
  base := (-4442604578177573661905319046740841219999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-6955731225959525520661716497004750000000000)
      constant := (43028559665042708143075329666044669600830361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree027.table
  base := (-4450895509156111085004101177026784120739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-6975788987923330769004050272789125000000000)
      constant := (43283345590285413589354333587011742065225721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127333717465371647901/50000000000000000000)
  centralHi := (254667434930743295803/100000000000000000000)
  directionLo := (129759339562467229483/50000000000000000000)
  directionHi := (259518679124934458967/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree028.table
  base := (-2442639065525794541317829567802508834463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-32462803526587648896943594313629500000000000)
      constant := (208098694435357392299000601346328305046829713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree028.table
  base := (-4892234908004277059102878061081529737651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-7234756981278238530935070800138500000000000)
      constant := (46518893452213278206941776013188270889707989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129759339562467229483/50000000000000000000)
  centralHi := (259518679124934458967/100000000000000000000)
  directionLo := (26428088696554848377/10000000000000000000)
  directionHi := (264280886965548483771/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree029.table
  base := (-1320523699384238026602884793249128944899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-33624816536357432950909464390737625000000000)
      constant := (223196977447795361987321944097870638631671298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree029.table
  base := (-264396238319146152655643898008242758401/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-749372497463314629286609132748787500000000)
      constant := (4989465468323353543346126933751019529215728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26428088696554848377/10000000000000000000)
  centralHi := (264280886965548483771/100000000000000000000)
  directionLo := (67239696987644200163/25000000000000000000)
  directionHi := (268958787950576800653/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree030.table
  base := (-1409055286435515549453532738596381531903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-3865203282903024111652814940871750000000000)
      constant := (26546469271123777864287877574454076596466034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree030.table
  base := (-176284408300305962589018797486305766361/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-3876346483994027027398555927418625000000000)
      constant := (26704748597045240251141889413514810784123864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67239696987644200163/25000000000000000000)
  centralHi := (268958787950576800653/100000000000000000000)
  directionLo := (54711341426212411359/20000000000000000000)
  directionHi := (68389176782765514199/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree031.table
  base := (-5950219742798404822520026130252559302819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-71897685111794002117682409089907750000000000)
      constant := (510516539044016421067631680853541735606391069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree031.table
  base := (-5954299925437180247056543536900752741469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-8011660961342961816728132382186625000000000)
      constant := (57062505445553533135521819859802684705642191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54711341426212411359/20000000000000000000)
  centralHi := (68389176782765514199/25000000000000000000)
  directionLo := (55615722387445793313/20000000000000000000)
  directionHi := (139039305968614483283/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree032.table
  base := (-3113082255601135879924453424430472332859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-37110855565666785112807074622062000000000000)
      constant := (272213746606382765257491947218069395390541109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree032.table
  base := (-3114786243503990669700375943410784215729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-4135314477348934789329576454768000000000000)
      constant := (30426469487835055029951335576542206898121831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55615722387445793313/20000000000000000000)
  centralHi := (139039305968614483283/50000000000000000000)
  directionLo := (141264076128259075383/50000000000000000000)
  directionHi := (282528152256518150767/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree033.table
  base := (-1293146796698369644309804947964064005997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-1701016381130514185189908653296450000000000)
      constant := (12879196796316861469917074834296951800085083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree033.table
  base := (-3234288863692194817236096912142896437923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-4264798474026388670295086718442687500000000)
      constant := (32390099446860379340109496763916842608566047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141264076128259075383/50000000000000000000)
  centralHi := (282528152256518150767/100000000000000000000)
  directionLo := (17931793432209292357/6250000000000000000)
  directionHi := (286908694915348677713/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree034.table
  base := (-6670286722879384345634771795783289668477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-78869763170412706441477629552556500000000000)
      constant := (615921212936619527263076340591085544992118227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree034.table
  base := (-1668164369087881942455088380430063620817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-4394282470703842551260596982117375000000000)
      constant := (34421900399576524862157711598902206956395126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17931793432209292357/6250000000000000000)
  centralHi := (286908694915348677713/100000000000000000000)
  directionLo := (5824467069821064621/2000000000000000000)
  directionHi := (291223353491053231051/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree035.table
  base := (-1710230584475913671874083004387922890191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-40596894594976137274704684853386375000000000)
      constant := (326747995945852667667472552880350880575163882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree035.table
  base := (-136857941298162862410235905932922419931/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-904753293476259286445221449158412500000000)
      constant := (7304335288747643538979293044437145832805795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5824467069821064621/2000000000000000000)
  centralHi := (291223353491053231051/100000000000000000000)
  directionLo := (295475014204452265531/100000000000000000000)
  directionHi := (73868753551113066383/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree036.table
  base := (-6978530852001688931365700834011109622003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-9279757245499093628593456651221000000000000)
      constant := (76920589001485475657533878878195801926456917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree036.table
  base := (-6980174366217975691420736364911126316377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-9306500928117500626383235018933500000000000)
      constant := (77378538246478805534891922852613786524787903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295475014204452265531/100000000000000000000)
  centralHi := (73868753551113066383/25000000000000000000)
  directionLo := (5993327170100680897/2000000000000000000)
  directionHi := (299666358505034044851/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree037.table
  base := (-1770958163855504526354980029319957496181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-42920920614515705382636425007602625000000000)
      constant := (366143399876846943350554271988877300955440862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree037.table
  base := (-3542599727598987040842285017695094396743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-4782734460736204194157127773141437500000000)
      constant := (40924550269557570857661900719013776489182027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5993327170100680897/2000000000000000000)
  centralHi := (299666358505034044851/100000000000000000000)
  directionLo := (37974985356361131513/12500000000000000000)
  directionHi := (60759976570177810421/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree038.table
  base := (-7157410838548438073676107521403015102329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1260)
      previous := (630)
      next := (630)
      square := (6756298766755452073207166580000000000000)
      linear := (-244226779081914068900843740081500000000000)
      constant := (2142655384077623822500455381508825989079039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree038.table
  base := (-7158546683787673007215823066812652233787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (140)
      previous := (70)
      next := (70)
      square := (750699862972828008134129620000000000000)
      linear := (-27214506689272343906496609622250000000000)
      constant := (239487070427521528805108432245738129016213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37974985356361131513/12500000000000000000)
  centralHi := (60759976570177810421/20000000000000000000)
  directionLo := (15393895804892944149/5000000000000000000)
  directionHi := (307877916097858882981/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree039.table
  base := (-449983585050527025842757243356271935801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-5027216292672808165618685017979875000000000)
      constant := (45328841628454129246647932457978627665031712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree039.table
  base := (-450042538972673689071578454814341231267/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-5041702454091111956088148300490812500000000)
      constant := (45597783095900183008864373183210665434257154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15393895804892944149/5000000000000000000)
  centralHi := (307877916097858882981/100000000000000000000)
  directionLo := (9746957338808720951/3125000000000000000)
  directionHi := (311902634841879070433/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree040.table
  base := (-7211194231137276822089033346881986570923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-92813919287650115089068070477854000000000000)
      constant := (859547225587119555511754427256346675631071173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree040.table
  base := (-7211977048897867179465862357498757622023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-10342372901537131674107317128331000000000000)
      constant := (96071166186961202481696136970540760998449697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9746957338808720951/3125000000000000000)
  centralHi := (311902634841879070433/100000000000000000000)
  directionLo := (63175215400298518589/20000000000000000000)
  directionHi := (157938038500746296473/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree041.table
  base := (-1438418130258537560538694441313997385011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-19027589061437936639399962126414050000000000)
      constant := (180876363576069413244006806863386845152349261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree041.table
  base := (-1438547981825032430618350589717730601889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-2120268178978407887207667531136075000000000)
      constant := (20216304536821769636002864526779373666780571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63175215400298518589/20000000000000000000)
  centralHi := (157938038500746296473/50000000000000000000)
  directionLo := (319800153881137461459/100000000000000000000)
  directionHi := (15990007694056873073/5000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree042.table
  base := (-3571338445862264929468798090437975532267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-5414553962596069516940641710349250000000000)
      constant := (52801228503509180488454150752095742395351613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree042.table
  base := (-111612735259181450926814824084507307509/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-5430154444123473598984679091514875000000000)
      constant := (53113273465273749277492225162999593849281032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319800153881137461459/100000000000000000000)
  centralHi := (15990007694056873073/5000000000000000000)
  directionLo := (323676660917875760421/100000000000000000000)
  directionHi := (161838330458937880211/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree043.table
  base := (-3531577761430827682240992983460998318489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-49892998673134409706431645470251375000000000)
      constant := (498833726492125380933076619116882163728854239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree043.table
  base := (-1412720270153342809348499380513983877883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-2223855376320370991980075742075825000000000)
      constant := (22301233427600866800472135123940177796646737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323676660917875760421/100000000000000000000)
  centralHi := (161838330458937880211/50000000000000000000)
  directionLo := (81876821820758530391/25000000000000000000)
  directionHi := (65501457456606824313/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree044.table
  base := (-695369050589441321078924396111447853357/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-10211002336580838752079503109471900000000000)
      constant := (104611730493369616189360761321913287174443107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree044.table
  base := (-6954059640058675248526189473014995866213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-11378244874956762721831399237728500000000000)
      constant := (116920325240208322880673901988221914617297107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81876821820758530391/25000000000000000000)
  centralHi := (65501457456606824313/20000000000000000000)
  directionLo := (331293624484441543847/100000000000000000000)
  directionHi := (41411703060555192981/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree045.table
  base := (-6814414551024105002186929958070894491113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-11603783265038661736525196805437250000000000)
      constant := (121752359748450824440230844080124082869958207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree045.table
  base := (-851840003358844247912194431181005108219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-5818606434155835241881209882538937500000000)
      constant := (61234487135095222612849290331875998252638014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331293624484441543847/100000000000000000000)
  centralHi := (41411703060555192981/12500000000000000000)
  directionLo := (167518587046769594831/50000000000000000000)
  directionHi := (335037174093539189663/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree046.table
  base := (-3322717536689779051425478885447692448801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-53379037702443761868329255701575750000000000)
      constant := (573314451199790487982677822380470298796345551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree046.table
  base := (-3322843872077974762258738123984044478879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-5948090430833289122846720146213625000000000)
      constant := (64076038119427334149857666727539691583749681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167518587046769594831/50000000000000000000)
  centralHi := (335037174093539189663/100000000000000000000)
  directionLo := (169369677351888175491/50000000000000000000)
  directionHi := (338739354703776350983/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree047.table
  base := (-1289367802772364166736622109157262248093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-21816420284885418368918050311473550000000000)
      constant := (239738003290655864781766372779321190112195843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree047.table
  base := (-3223523954391440573757733958050765569469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-6077574427510743003812230409888312500000000)
      constant := (66984800209505710272165102534523523727077941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169369677351888175491/50000000000000000000)
  centralHi := (338739354703776350983/100000000000000000000)
  directionLo := (2739212065693953607/800000000000000000)
  directionHi := (85600377052936050219/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree048.table
  base := (-1243739348247804703499648712974640130297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-2475691720977036887833822038035200000000000)
      constant := (27821207805978329074970684207032754912962783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree048.table
  base := (-777358670801120877587821377742676690811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-6207058424188196884777740673563000000000000)
      constant := (69960760978689187000373404930286699858468916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2739212065693953607/800000000000000000)
  centralHi := (85600377052936050219/25000000000000000000)
  directionLo := (69204981099982522391/20000000000000000000)
  directionHi := (86506226374978152989/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree049.table
  base := (-2980532605292527222793372987472532153831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-56865076731753114030226865932900125000000000)
      constant := (653210860899891183150749973341313580922828081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree049.table
  base := (-1192241560298878774684273335093786011529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-2534616968346260306297300374895075000000000)
      constant := (29201564150373080251934495209791045788900531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69204981099982522391/20000000000000000000)
  centralHi := (86506226374978152989/25000000000000000000)
  directionLo := (174805375794603192829/50000000000000000000)
  directionHi := (349610751589206385659/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree050.table
  base := (-2836995259892936272487934851052771616227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-58027089741522898084192736010008250000000000)
      constant := (681045989136760258569188897243577396581378477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree050.table
  base := (-2837054126453495160771342569546464971379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-6466026417543104646708761200912375000000000)
      constant := (76114240271720608095388916954731470285957181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174805375794603192829/50000000000000000000)
  centralHi := (349610751589206385659/100000000000000000000)
  directionLo := (176580095160323844229/50000000000000000000)
  directionHi := (353160190320647688459/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree051.table
  base := (-2678754989413820360508372943869600675837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-6576566972365853570906511787457375000000000)
      constant := (78831388859449678755823805980649912046647843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree051.table
  base := (-5357607148724286578662374992329636656333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-13191020828441117055348542929174125000000000)
      constant := (158583488181569830386954782104891177924876287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176580095160323844229/50000000000000000000)
  centralHi := (353160190320647688459/100000000000000000000)
  directionLo := (178337154308813632593/50000000000000000000)
  directionHi := (356674308617627265187/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree052.table
  base := (-5011653784718945786878756135445886770971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-120702231522124932384248952328449000000000000)
      constant := (1477040687279422569144864765346162126381115221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree052.table
  base := (-1252933488031503804232894044906843213631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-6724994410898012408639781728261750000000000)
      constant := (82536416515021680194828379557647048262258418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178337154308813632593/50000000000000000000)
  centralHi := (356674308617627265187/100000000000000000000)
  directionLo := (360154140373824858727/100000000000000000000)
  directionHi := (45019267546728107341/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree053.table
  base := (-231822318860197720289493099078521428101/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-12302625754166450049218069248266525000000000)
      constant := (153631896229677677426965892053896157213324702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree053.table
  base := (-4636512492707291437590585861808582335243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-13708956815150932579210583983872875000000000)
      constant := (171696506486377969611236017665614794159789777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360154140373824858727/100000000000000000000)
  centralHi := (45019267546728107341/12500000000000000000)
  directionLo := (181800335003098291249/50000000000000000000)
  directionHi := (363600670006196582499/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree054.table
  base := (-4231907536100313132365886080694608820459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-13927809284578229844456936959653500000000000)
      constant := (177422195584169922147029351713928949340814301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree054.table
  base := (-4231962043336456923192614328720209969247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-13967924808505840341141604511222250000000000)
      constant := (178454501593068186704290848841218523732351833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181800335003098291249/50000000000000000000)
  centralHi := (363600670006196582499/100000000000000000000)
  directionLo := (91753708926908434621/25000000000000000000)
  directionHi := (73402967141526747697/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree055.table
  base := (-3798053269502198073918927258220477184689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-127674309580743636708044172791097750000000000)
      constant := (1658483029151382166133023490921627782908195439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree055.table
  base := (-474762273898810308876474843691148480783/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-7113446400930374051536312519285812500000000)
      constant := (92673406361571562605502644562018011378905598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91753708926908434621/25000000000000000000)
  centralHi := (73402967141526747697/20000000000000000000)
  directionLo := (46299691553718750683/12500000000000000000)
  directionHi := (74079506485950001093/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree056.table
  base := (-333489653270493407760965175762830039853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-12999833560028320481597591294531400000000000)
      constant := (172136872688658086427051189240269590200517603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree056.table
  base := (-3334933542305951704753922489222048732991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-14485860795215655865003645565921000000000000)
      constant := (192373435325823578443221550719307152907390249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46299691553718750683/12500000000000000000)
  centralHi := (74079506485950001093/20000000000000000000)
  directionLo := (46718701827833697867/12500000000000000000)
  directionHi := (373749614622669582937/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree057.table
  base := (-1421223905055983285851903570053908544269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (70)
      previous := (35)
      next := (35)
      square := (375349931486414004067064810000000000000)
      linear := (-20363552111391624026455471391125000000000)
      constant := (274770209202723699528977216996346482080731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree057.table
  base := (-710619572866309052234007148519149873443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (70)
      previous := (35)
      next := (35)
      square := (375349931486414004067064810000000000000)
      linear := (-20422200538186376214590950267687500000000)
      constant := (276363387424921205344776982115409454159364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46718701827833697867/12500000000000000000)
  centralHi := (373749614622669582937/100000000000000000000)
  directionLo := (75414379751116524283/20000000000000000000)
  directionHi := (47133987344447827677/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree058.table
  base := (-2320715586236864140047219353202038811709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-134646387639362341031839393253746500000000000)
      constant := (1850747279123350787610454593336751154025757459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree058.table
  base := (-2320740683155996631706965662308237666669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-15003796781925471388865686620619750000000000)
      constant := (206829600931791675164145845884135683233582491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75414379751116524283/20000000000000000000)
  centralHi := (47133987344447827677/12500000000000000000)
  directionLo := (380365165639135089321/100000000000000000000)
  directionHi := (190182582819567544661/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree059.table
  base := (-553033352167685425808235574251665741/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-13697041365890190913977113340796275000000000)
      constant := (191724008375156814406574773806935505115522120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree059.table
  base := (-176972738442297324872569766880398882341/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-1526276477528037915079670714796912500000000)
      constant := (21425913855201612191935925911480310866756149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380365165639135089321/100000000000000000000)
  centralHi := (190182582819567544661/50000000000000000000)
  directionLo := (191815081284184348391/50000000000000000000)
  directionHi := (383630162568368696783/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree060.table
  base := (-59471339399212492864339150476332294561/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-1547715996427127524974476372913100000000000)
      constant := (22054835724813820902693369393997869333326958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree060.table
  base := (-297360946613005264478842561681087696237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-7760866384317643456363863837659250000000000)
      constant := (110911488317624178435159482602878481245816886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191815081284184348391/50000000000000000000)
  centralHi := (383630162568368696783/100000000000000000000)
  directionLo := (19343380265143636259/5000000000000000000)
  directionHi := (386867605302872725181/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree061.table
  base := (-289940132414507463506863678228802237729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-70809232848990522677817306858197625000000000)
      constant := (1026916329481331804543706007072125225045243479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree061.table
  base := (-579894248507813253969636743698881130257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-15780700761990194674658748202667875000000000)
      constant := (229521113607793832993740555298502974419789723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19343380265143636259/5000000000000000000)
  centralHi := (386867605302872725181/100000000000000000000)
  directionLo := (195039089949505787947/50000000000000000000)
  directionHi := (78015635979802315179/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree062.table
  base := (58929205247956471307559065692553593579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-143942491717520613463566353870611500000000000)
      constant := (2123932403122300855145723893695032559750538171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree062.table
  base := (58917704756760582766856164442331561703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-16039668755345102436589768730017250000000000)
      constant := (237353548197252857151119611943066482475024783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195039089949505787947/50000000000000000000)
  centralHi := (78015635979802315179/20000000000000000000)
  directionLo := (98315636101878512627/25000000000000000000)
  directionHi := (393262544407514050509/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree063.table
  base := (726998679509136346180201907525665913467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-16251835304117797952388677113869750000000000)
      constant := (243914937572355710108107282150106659926011587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree063.table
  base := (11359206620426629108032023019031448787/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-8149318374350005099260394628683312500000000)
      constant := (122660139687453706159044966919414873269043674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98315636101878512627/25000000000000000000)
  centralHi := (393262544407514050509/100000000000000000000)
  directionLo := (79284266089664545131/20000000000000000000)
  directionHi := (49552666306040340707/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree064.table
  base := (712162888662083433578262609126686154141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-74295271878299874839714917089522000000000000)
      constant := (1133869378157348591989006225973960603314804109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree064.table
  base := (284863600928378386960664399970212047447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-3311520948410983592090361956943200000000000)
      constant := (50684261261824220652439829747762046549128367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79284266089664545131/20000000000000000000)
  centralHi := (49552666306040340707/12500000000000000000)
  directionLo := (399555144673378726467/100000000000000000000)
  directionHi := (99888786168344681617/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree065.table
  base := (2150908572977323427343528599771073397521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-150914569776139317787361574333260250000000000)
      constant := (2341445351356137844913069273192474518249795729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree065.table
  base := (86036087415251064685585744330456321981/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-3363314547081965144476566062413075000000000)
      constant := (52331325665529444364639950152776607450238205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399555144673378726467/100000000000000000000)
  centralHi := (99888786168344681617/25000000000000000000)
  directionLo := (201332285063468476021/50000000000000000000)
  directionHi := (402664570126936952043/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree066.table
  base := (581349101781536680615941423049836224099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-3405302128792864131006518099721700000000000)
      constant := (53696760404777954137196883856552456501899739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree066.table
  base := (726685065204692142668242559567147435023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-8537770364382366742156925419707375000000000)
      constant := (135013122443571126502611237004161505838711606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201332285063468476021/50000000000000000000)
  centralHi := (402664570126936952043/100000000000000000000)
  directionLo := (40575016751205075551/10000000000000000000)
  directionHi := (405750167512050755511/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree067.table
  base := (3691835325487709029687199414798697162259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-155562621815218454003225054641692750000000000)
      constant := (2492465352798777587562945581479289924111429491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree067.table
  base := (230739438413418289997442493124663377251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-8667254361059820623122435683382062500000000)
      constant := (139265077774253787038575977165087100587407138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40575016751205075551/10000000000000000000)
  centralHi := (405750167512050755511/100000000000000000000)
  directionLo := (408812476371017290323/100000000000000000000)
  directionHi := (102203119092754322581/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree068.table
  base := (4506177004188131681874489093891707691247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-157886647834758022111156794795909000000000000)
      constant := (2569778751798245205316754560197451470788861503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree068.table
  base := (4506173463949511217750297739431261721279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-17593476715474549008175891894113500000000000)
      constant := (287168359956945331962771781117969638606381719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408812476371017290323/100000000000000000000)
  centralHi := (102203119092754322581/25000000000000000000)
  directionLo := (205926008093410758149/50000000000000000000)
  directionHi := (411852016186821516299/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree069.table
  base := (5349769721577761641388713820524320741277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-17801185983810843357676503883347250000000000)
      constant := (294254934726453650448964795553629393068850997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree069.table
  base := (1337441703709878197724170891275660110817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-8926222354414728385053456210731437500000000)
      constant := (147970428912913703402917412975878263416416124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205926008093410758149/50000000000000000000)
  centralHi := (411852016186821516299/100000000000000000000)
  directionLo := (414869287411946431997/100000000000000000000)
  directionHi := (207434643705973215999/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree070.table
  base := (15556532030232743511883877128933635989/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-16253469987383715832702027510434150000000000)
      constant := (272801233285587471734993680824252223145630440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree070.table
  base := (6222610425996050801991425390076785790619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-18111412702184364532037932948812250000000000)
      constant := (304847648923648597199117229707862426701663459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414869287411946431997/100000000000000000000)
  centralHi := (207434643705973215999/50000000000000000000)
  directionLo := (20893238621515964977/5000000000000000000)
  directionHi := (417864772430319299541/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree071.table
  base := (71247057379061900360233736891655314741/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-16485872589337672643495201525855775000000000)
      constant := (280893251100421778915162816448543330004060090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree071.table
  base := (1781175944898804710007526474185301985199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-9185190347769636146984476738080812500000000)
      constant := (156944366531737236464123198867314614693469928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20893238621515964977/5000000000000000000)
  centralHi := (417864772430319299541/100000000000000000000)
  directionLo := (420838936457629664167/100000000000000000000)
  directionHi := (52604867057203708021/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree072.table
  base := (8056048064537791322042460028089815189081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-18575861323657366060320417268086000000000000)
      constant := (321228327285720999111246031882418673283258241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree072.table
  base := (2014011614409248317144624577391807446731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-9314674344447090027949987001755500000000000)
      constant := (161532055047203512730234787083045541226539782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420838936457629664167/100000000000000000000)
  centralHi := (52604867057203708021/12500000000000000000)
  directionLo := (423792228384777226149/100000000000000000000)
  directionHi := (8475844567695544523/2000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree073.table
  base := (2254159860280168567398296038629368123517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-84753388966227931325407747783495125000000000)
      constant := (1487189817708860352698865554833648315707238466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree073.table
  base := (9016638122825359883262035025222677648239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-18888316682249087817830994530860375000000000)
      constant := (332373779894682393668007540097445071201326779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423792228384777226149/100000000000000000000)
  centralHi := (8475844567695544523/2000000000000000000)
  directionLo := (426725081568779481557/100000000000000000000)
  directionHi := (213362540784389740779/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree074.table
  base := (2501619896106682830754878489390050116683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-85915401975997715379373617860603250000000000)
      constant := (1529453289811352403946426092166871459720706134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree074.table
  base := (10006478503105169466824618766139717122743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-19147284675603995579762015058209750000000000)
      constant := (341817742366088668683430844411489207412560223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426725081568779481557/100000000000000000000)
  centralHi := (213362540784389740779/50000000000000000000)
  directionLo := (429637914575084753361/100000000000000000000)
  directionHi := (214818957287542376681/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree075.table
  base := (11025568265940395062729106865189060726311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-19350536663503888762964330652824750000000000)
      constant := (349403975271554913437813554436064989203448271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree075.table
  base := (2756391844789165332362902531129447601173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-9703126334479451670846517792779562500000000)
      constant := (175697998714725708448858201141003744859453156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429637914575084753361/100000000000000000000)
  centralHi := (214818957287542376681/50000000000000000000)
  directionLo := (27033195742180672809/6250000000000000000)
  directionHi := (86506226374978152989/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree076.table
  base := (12073905301397668733342286703501127992399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1260)
      previous := (630)
      next := (630)
      square := (6756298766755452073207166580000000000000)
      linear := (-488861096928184396051553229999000000000000)
      constant := (8951709773636884263384797669115822651931591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree076.table
  base := (12073904574282214481042343411813994403681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (140)
      previous := (70)
      next := (70)
      square := (750699862972828008134129620000000000000)
      linear := (-54474295463473160951867191448500000000000)
      constant := (1000300678728484202585700480319767119403681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27033195742180672809/6250000000000000000)
  centralHi := (86506226374978152989/20000000000000000000)
  directionLo := (87081024900151575521/20000000000000000000)
  directionHi := (217702562250378938803/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree077.table
  base := (6575745271160367863305995734860984157331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-89401441005307067541271228091927625000000000)
      constant := (1659850465828531688078713692882705003542793419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree077.table
  base := (6575744973113983761827396773385863298407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-9962094327834359432777538320128937500000000)
      constant := (185477692544664582712969093348720447529631177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87081024900151575521/20000000000000000000)
  centralHi := (217702562250378938803/50000000000000000000)
  directionLo := (219130135331762841143/50000000000000000000)
  directionHi := (438260270663525682287/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree078.table
  base := (14258323869167704725422036724304486426523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-20125212003350411465608244037563500000000000)
      constant := (378781876353116343030839754258254497724974803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree078.table
  base := (14258323380570371877303220425554889247341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-20183156649023626627486097167607250000000000)
      constant := (380936517593183620737842490010537553299540101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219130135331762841143/50000000000000000000)
  centralHi := (438260270663525682287/100000000000000000000)
  directionLo := (55137117041661054467/12500000000000000000)
  directionHi := (441096936333288435737/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree079.table
  base := (1924300648223695087916716941967822430963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-91725467024846635649202968246143875000000000)
      constant := (1749787547266739101310701936193495033203420148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree079.table
  base := (7697202392684228424137450931159829024201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-10221062321189267194708558847478312500000000)
      constant := (195525971249677736324360245312818142125392811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55137117041661054467/12500000000000000000)
  centralHi := (441096936333288435737/100000000000000000000)
  directionLo := (22195773789347795211/5000000000000000000)
  directionHi := (443915475786955904221/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree080.table
  base := (8279867207472542668807703159172159530937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-92887480034616419703168838323252000000000000)
      constant := (1795657776736200001929205202240797846316014313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree080.table
  base := (16559734086839782990806496254592539978469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-20701092635733442151348138222306000000000000)
      constant := (401301659781209260518651622224244156932227309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22195773789347795211/5000000000000000000)
  centralHi := (443915475786955904221/100000000000000000000)
  directionLo := (8934324642494378391/2000000000000000000)
  directionHi := (446716232124718919551/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree081.table
  base := (17754311494672017472144850531630295078687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-20899887343196934168252157422302250000000000)
      constant := (409362029310388567165815151283343306054656007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree081.table
  base := (17754311225864325485439218475399232154409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-20960060629088349913279158749655375000000000)
      constant := (411685669417402655387811263375523448003054149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8934324642494378391/2000000000000000000)
  centralHi := (446716232124718919551/100000000000000000000)
  directionLo := (17979981510302042691/4000000000000000000)
  directionHi := (112374884439387766819/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree082.table
  base := (1186133523459448559477636205333086013297/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-95211506054155987811100578477468250000000000)
      constant := (1889201612667778394099338692293990673220115624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree082.table
  base := (3795627231031590283094603961782479198471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-4243805724488651535042035855400950000000000)
      constant := (84440794278173217054654139298612097646898031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17979981510302042691/4000000000000000000)
  centralHi := (112374884439387766819/25000000000000000000)
  directionLo := (113066428716926847/25000000000000000)
  directionHi := (452265714867707388001/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree083.table
  base := (20231209017331399042456334527257102166167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-192747038127851543730132897109152750000000000)
      constant := (3873750437969752420757801185983723156969126583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree083.table
  base := (20231208836987424054361549678155934494349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-21477996615798165437141199804354125000000000)
      constant := (432856565687977851716746689018566906610272489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113066428716926847/25000000000000000)
  centralHi := (452265714867707388001/100000000000000000000)
  directionLo := (91003015168805197441/20000000000000000000)
  directionHi := (227507537922012993603/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree084.table
  base := (4302705877801663699743561073897290953107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-4334912536608691374179214161408200000000000)
      constant := (88228886702075587099686171663609784534071627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree084.table
  base := (10756764620661675365271826303374971637711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-10868482304576536599536110165851750000000000)
      constant := (221821726148948671981902831912534778823713671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91003015168805197441/20000000000000000000)
  centralHi := (227507537922012993603/50000000000000000000)
  directionLo := (22887396184684871411/5000000000000000000)
  directionHi := (457747923693697428221/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree085.table
  base := (36520155944432692286375235642831382147/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-39479018033386135989199275483517050000000000)
      constant := (813610323224983302460172343460822523980700375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree085.table
  base := (22825097344347294362544874285379618300309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-21995932602507980961003240859052875000000000)
      constant := (454564631212026106228035342906905797089224049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22887396184684871411/5000000000000000000)
  centralHi := (457747923693697428221/100000000000000000000)
  directionLo := (57558069054004789759/12500000000000000000)
  directionHi := (460464552432038318073/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree086.table
  base := (24165913226242377061187744093870769541957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-199719116186470248053928117571801500000000000)
      constant := (4167005581499722639870551823295378958366818293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree086.table
  base := (2416591312724528684858062263548100941359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-2225490059586288872293426138640225000000000)
      constant := (46562010242357229602469148852371403892955599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57558069054004789759/12500000000000000000)
  centralHi := (460464552432038318073/100000000000000000000)
  directionLo := (463165247451688334557/100000000000000000000)
  directionHi := (231582623725844167279/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree087.table
  base := (6383994164067176184612524652533959865981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-11224619011444989786769992095889875000000000)
      constant := (237064544314830847510805747806879122538863282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree087.table
  base := (6383994143808234670329667421952020341047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-11256934294608898242432640956875812500000000)
      constant := (238404932963599374370813583189298232221392184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463165247451688334557/100000000000000000000)
  centralHi := (231582623725844167279/50000000000000000000)
  directionLo := (93170057174508594209/20000000000000000000)
  directionHi := (232925142936271485523/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree088.table
  base := (26935287743092273539106916513786571771419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-204367168225549384269791597880234000000000000)
      constant := (4368520264586790903356978118395480821685340331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree088.table
  base := (26935287676767818682611634468602972083969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-22772836582572704246796302441101000000000000)
      constant := (488133921718738646723531171940026485422312809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93170057174508594209/20000000000000000000)
  centralHi := (232925142936271485523/50000000000000000000)
  directionLo := (468519936873636500299/100000000000000000000)
  directionHi := (4685199368736365003/1000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree089.table
  base := (28363846477190095575265114602266989866919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-206691194245088952377723338034450250000000000)
      constant := (4471080982228289396710211169585244438358869831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree089.table
  base := (14181923211456627000248242004305535657809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-11515902287963806004363661484225187500000000)
      constant := (249796134897482925535422425153051593782625299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468519936873636500299/100000000000000000000)
  centralHi := (4685199368736365003/1000000000000000000)
  directionLo := (18846978480324007761/4000000000000000000)
  directionHi := (235587231004050097013/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree090.table
  base := (116490831450142918263106947476026368149/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-11611956681368251138091948788259250000000000)
      constant := (254157997253758328532242995103436952981928992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree090.table
  base := (1491082640341227819442422475196170201317/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-2329077256928251977065834349579975000000000)
      constant := (51118491015340942932671715993861543088475874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18846978480324007761/4000000000000000000)
  centralHi := (235587231004050097013/50000000000000000000)
  directionLo := (236907057751119444709/50000000000000000000)
  directionHi := (473814115502238889419/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree091.table
  base := (31308706859669889228327622318365571683233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-211339246284168088593586818342882750000000000)
      constant := (4679809169586801974690364615648216261930074017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree091.table
  base := (31308706823334226020481177073087104500007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-23549740562637427532589364023149125000000000)
      constant := (522911842792203914053533827086358730857315027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236907057751119444709/50000000000000000000)
  centralHi := (473814115502238889419/100000000000000000000)
  directionLo := (47643914453969385933/10000000000000000000)
  directionHi := (476439144539693859331/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree092.table
  base := (32825008498341570798918990536164559357099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-213663272303707656701518558497099000000000000)
      constant := (4785976639272267326956814263880921965851214651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree092.table
  base := (4103126058577146148883462339449712174531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-11904354277996167647260192275249250000000000)
      constant := (267386533854984223212016408150575485942522764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47643914453969385933/10000000000000000000)
  centralHi := (476439144539693859331/100000000000000000000)
  directionLo := (59881223691448873031/12500000000000000000)
  directionHi := (479049789531590984249/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree093.table
  base := (34370557764233778758491443777200741871919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-23998588702583024978827810961257250000000000)
      constant := (543705151068248996209964207383524518597012759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree093.table
  base := (34370557739920593894360780075213172575539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-24067676549347243056451405077847875000000000)
      constant := (546768584905709268523958875980388788307582079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59881223691448873031/12500000000000000000)
  centralHi := (479049789531590984249/100000000000000000000)
  directionLo := (48164628437350987303/10000000000000000000)
  directionHi := (481646284373509873031/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree094.table
  base := (35945354655230942710117329458164433055291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-218311324342786792917382038805531500000000000)
      constant := (5001918330605849403269337480117439196121640459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree094.table
  base := (561646166177284082773714471941396955243/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-12163322271351075409191212802598625000000000)
      constant := (279449197189370543627327896623979105517592136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48164628437350987303/10000000000000000000)
  centralHi := (481646284373509873031/100000000000000000000)
  directionLo := (484228856690051323969/100000000000000000000)
  directionHi := (48422885669005132397/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree095.table
  base := (37549399169935598933458952183272764146497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1260)
      previous := (630)
      next := (630)
      square := (6756298766755452073207166580000000000000)
      linear := (-611178255851319559626907974957750000000000)
      constant := (14159813164106793017918049674618224408568473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree095.table
  base := (2346837447104656512416977989831168357033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (70)
      previous := (35)
      next := (35)
      square := (375349931486414004067064810000000000000)
      linear := (-34052094925286784737276241180812500000000)
      constant := (791083789651833364814750167699511163262514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484228856690051323969/100000000000000000000)
  centralHi := (48422885669005132397/10000000000000000000)
  directionLo := (243398864033863449333/50000000000000000000)
  directionHi := (486797728067726898667/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree096.table
  base := (9795672826879972722413339217749141587181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-12386632021214773840735862172998000000000000)
      constant := (290148279140092216032897082369502880225944682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree096.table
  base := (39182691294223582845990605370136263434017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-24844580529411966342244466659896000000000000)
      constant := (583560890155110880258329029276530191099680137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243398864033863449333/50000000000000000000)
  centralHi := (486797728067726898667/100000000000000000000)
  directionLo := (244676557138422492323/50000000000000000000)
  directionHi := (489353114276844984647/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree097.table
  base := (20422615533802957206131575210048197665317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-112641701200702748620588629634090125000000000)
      constant := (2667423873720972210001888520136565369605239933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree097.table
  base := (40845231056735020779485533096690467886739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-25103548522766874104175487187245375000000000)
      constant := (596093576458109378718837965120515740352425279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244676557138422492323/50000000000000000000)
  centralHi := (489353114276844984647/100000000000000000000)
  directionLo := (245947612741511087779/50000000000000000000)
  directionHi := (491895225483022175559/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree098.table
  base := (42537018450169379931142109293119812460171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-227607428420945065349108999422396500000000000)
      constant := (5448228721003326956889899525130232723808095579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree098.table
  base := (42537018441282418785061483507895170962411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-25362516516121781866106507714594750000000000)
      constant := (608760555037645754661488152560230832498680371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245947612741511087779/50000000000000000000)
  centralHi := (491895225483022175559/100000000000000000000)
  directionLo := (494424266448906763841/100000000000000000000)
  directionHi := (247212133224453381921/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree099.table
  base := (44258053455462119503385402636515347409441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-25547939382276070384115637730734750000000000)
      constant := (618090216134069522400446349086574341196058201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree099.table
  base := (11064513362049445093783136154613692210573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-12810742254738344814018764120972062500000000)
      constant := (310780912946919930677130538684491877279939956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494424266448906763841/100000000000000000000)
  centralHi := (247212133224453381921/50000000000000000000)
  directionLo := (496940436726662315771/100000000000000000000)
  directionHi := (124235109181665578943/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree100.table
  base := (23004168041974910283699513410344240446463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-116127740230012100782486239865414500000000000)
      constant := (2839298710026676836316755486213693593460558287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree100.table
  base := (46008336078012443334276181663998835429089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-25880452502831597389968548769293500000000000)
      constant := (634497389026883511737389204496836782714901129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496940436726662315771/100000000000000000000)
  centralHi := (124235109181665578943/25000000000000000000)
  directionLo := (499443930841723408083/100000000000000000000)
  directionHi := (124860982710430852021/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree101.table
  base := (4778786633626205956457828867825682253321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-23457950647956376967290421988504525000000000)
      constant := (579558514554555636383647436897406168594164929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree101.table
  base := (93335676428534640469422679291151614757/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-13069710248093252575949784648321437500000000)
      constant := (323783622218511693655978556067928835695789162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499443930841723408083/100000000000000000000)
  centralHi := (124860982710430852021/25000000000000000000)
  directionLo := (125483734617075600007/25000000000000000000)
  directionHi := (501934938468302400029/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree102.table
  base := (49596644213152267946353889367175655489687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-26322614722122593086759551115473500000000000)
      constant := (657086124631742408222067297720154364756777007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree102.table
  base := (49596644209187093322435859391516163826519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-26398388489541412913830589823992250000000000)
      constant := (660771392124547362181229403685005917172623359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125483734617075600007/25000000000000000000)
  centralHi := (501934938468302400029/100000000000000000000)
  directionLo := (504413644597095369267/100000000000000000000)
  directionHi := (126103411149273842317/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree103.table
  base := (6429333714433214467597130435901751156647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-119613779259321452944383850096738875000000000)
      constant := (3016583674238237942720521650092009777172409412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree103.table
  base := (51434669712225804237766389587518288469327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-26657356482896320675761610351341625000000000)
      constant := (674109832089773581564901006459886442957739547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504413644597095369267/100000000000000000000)
  centralHi := (126103411149273842317/25000000000000000000)
  directionLo := (126720057423901712507/25000000000000000000)
  directionHi := (506880229695606850029/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree104.table
  base := (10660388568822792827816974410648361112931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-48310316907636494799339888069538800000000000)
      constant := (1230752365184180132094823327451852975255912819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree104.table
  base := (53301942841466908586967737648113936732391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-26916324476251228437692630878691000000000000)
      constant := (687582564333041760874319976890455943660393151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126720057423901712507/25000000000000000000)
  centralHi := (506880229695606850029/100000000000000000000)
  directionLo := (127333717465371647901/25000000000000000000)
  directionHi := (101866973972297318321/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree105.table
  base := (27599231800027267473576873197873524245163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-13548645030984557894701732250106125000000000)
      constant := (348642141890114832635839890064437820768128843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree105.table
  base := (3449903974868253208316081999983078909927/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-13587646234803068099811825703020187500000000)
      constant := (350594794427353136970567799709327130427025426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127333717465371647901/25000000000000000000)
  centralHi := (101866973972297318321/20000000000000000000)
  directionLo := (127944434242311758973/25000000000000000000)
  directionHi := (511777736969247035893/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree106.table
  base := (28562115992137392279286335136959589668361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-123099818288630805106281460328063250000000000)
      constant := (3199278766391591393638409062549736870895004889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree106.table
  base := (11424846396501665391335963551455885606891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-5486852092592208792310934386677950000000000)
      constant := (142986181131026136374572122518193153610337651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127944434242311758973/25000000000000000000)
  centralHi := (511777736969247035893/100000000000000000000)
  directionLo := (514208998810707440727/100000000000000000000)
  directionHi := (64276124851338430091/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree107.table
  base := (7384905999722395516693857188085211951399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-124261831298400589160247330405171375000000000)
      constant := (3261379381103755760894368342384614111786006404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree107.table
  base := (59079247996336334765392268315874463389301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-27693228456315951723485692460739125000000000)
      constant := (728806514734683421019523098243025186166350161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514208998810707440727/100000000000000000000)
  centralHi := (64276124851338430091/12500000000000000000)
  directionLo := (258314409614744705659/50000000000000000000)
  directionHi := (516628819229489411319/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree108.table
  base := (7632938955197400580342047447683510890229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-13935982700907819246023688942475500000000000)
      constant := (369342346794352203061361626913961645975490676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree108.table
  base := (30531755820200407643182676106932898360977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-13976098224835429742708356494044250000000000)
      constant := (371408208046867211355715837468588690370812697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258314409614744705659/50000000000000000000)
  centralHi := (516628819229489411319/100000000000000000000)
  directionLo := (519037358249868917933/100000000000000000000)
  directionHi := (259518679124934458967/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree109.table
  base := (63077022916685692424399335028729006114071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-253171714635880314536358141118775250000000000)
      constant := (6774767973058951232037175474251658122895866679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree109.table
  base := (63077022915723359310893519660743851884971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-28211164443025767247347733515437875000000000)
      constant := (756960609732652481224243639199048394788287031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519037358249868917933/100000000000000000000)
  centralHi := (259518679124934458967/50000000000000000000)
  directionLo := (130358693050067889409/25000000000000000000)
  directionHi := (521434772200271557637/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree110.table
  base := (65119781824102603627146169488470271530297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-255495740655419882644289881272991500000000000)
      constant := (6902575954492608171093557596061150615326934953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree110.table
  base := (65119781823316779226207770004063225435883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-28470132436380675009278754042787250000000000)
      constant := (771239095651803221829749381793105437663603763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130358693050067889409/25000000000000000000)
  centralHi := (521434772200271557637/100000000000000000000)
  directionLo := (104764242766336151087/20000000000000000000)
  directionHi := (130955303457920188859/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree111.table
  base := (33595894182411224498850700136948962754599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-14323320370831080597345645634844875000000000)
      constant := (390643677033474174427209089257244085320035239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree111.table
  base := (67191788364180811534176412466389056606181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-28729100429735582771209774570136625000000000)
      constant := (785651873851547549405123362348694524630143841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104764242766336151087/20000000000000000000)
  centralHi := (130955303457920188859/25000000000000000000)
  directionLo := (105239366486242539699/20000000000000000000)
  directionHi := (4110912753368849207/781250000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree112.table
  base := (13858608507964549534200021597597004302061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-52028758538899803772030672316284800000000000)
      constant := (1432359733878381619499039516567689266977396189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree112.table
  base := (6929304253929888351576792768965200451759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-2898806842309049053314079509748600000000000)
      constant := (80019894433224048119879520237755262363084999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105239366486242539699/20000000000000000000)
  centralHi := (4110912753368849207/781250000000000000)
  directionLo := (528561773931096967541/100000000000000000000)
  directionHi := (264280886965548483771/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree113.table
  base := (71423544350063402960165926564499943589071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-262467818714038586968085101735640250000000000)
      constant := (7293213402863845770374198211336122492502141679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree113.table
  base := (17855886087408932191192347770885297044437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-14623518208222699147535907812417687500000000)
      constant := (407440153547115143019061018051288753313739764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528561773931096967541/100000000000000000000)
  centralHi := (264280886965548483771/50000000000000000000)
  directionLo := (265458090506643995471/50000000000000000000)
  directionHi := (530916181013287990943/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree114.table
  base := (73583293796484797080976975799485583351911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (140)
      previous := (70)
      next := (70)
      square := (750699862972828008134129620000000000000)
      linear := (-81499490530494969244695857768500000000000)
      constant := (2285574141896399956954702555660438708351911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree114.table
  base := (14716658759227135627560615504680886559759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (28)
      previous := (14)
      next := (14)
      square := (150139972594565601626825924000000000000)
      linear := (-16346816847534795599447554654950000000000)
      constant := (459665352984962807402960944461922292809759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265458090506643995471/50000000000000000000)
  centralHi := (530916181013287990943/100000000000000000000)
  directionLo := (106652038641983904977/20000000000000000000)
  directionHi := (266630096604959762443/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree115.table
  base := (15154458176001291453045249412926794180213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-53423174150623544636789716408814550000000000)
      constant := (1511929924373513742157236837563800470697762037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree115.table
  base := (15154458175944297290724966630169329657131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-5952994480631042763786771335906825000000000)
      constant := (168929181892691267932206693757649738357786791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106652038641983904977/20000000000000000000)
  centralHi := (266630096604959762443/50000000000000000000)
  directionLo := (535593946999802289307/100000000000000000000)
  directionHi := (133898486749950572327/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree116.table
  base := (124784856962441879083626214043919899377/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-53887979354531458258376064439657800000000000)
      constant := (1538934221481051688995199340646861331634484125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree116.table
  base := (19497633900323395640601173107282775739657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-15011970198255060790432438603441750000000000)
      constant := (429865074535675378874550155323626203146532354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535593946999802289307/100000000000000000000)
  centralHi := (133898486749950572327/25000000000000000000)
  directionLo := (67239696987644200163/12500000000000000000)
  directionHi := (107583515180230720261/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree117.table
  base := (80238027961919478748727385155517261755159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-30195991421355206599979118039167250000000000)
      constant := (870099427070813028919486890782734219774862399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree117.table
  base := (80238027961729652440097650430904632031757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-30282908389865029342795897734232875000000000)
      constant := (874948680961857966263864783552006389546276777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67239696987644200163/12500000000000000000)
  centralHi := (107583515180230720261/20000000000000000000)
  directionLo := (540231210560737288091/100000000000000000000)
  directionHi := (135057802640184322023/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree118.table
  base := (1031434599525492441131555809489811404079/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-27408794881173642750774380250672150000000000)
      constant := (796832083056651663510725365810748010827321368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree118.table
  base := (82514767961884482750858112973515090885763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-30541876383219937104726918261582250000000000)
      constant := (890301505135286543191086628002573217341010443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540231210560737288091/100000000000000000000)
  centralHi := (135057802640184322023/25000000000000000000)
  directionLo := (54253497883958227743/10000000000000000000)
  directionHi := (542534978839582277431/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree119.table
  base := (42410377801358208940315965609818277848539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-138205987415637997807837771330468875000000000)
      constant := (4053474534097777421959350077582819391370528211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree119.table
  base := (84820755602590006675855513576126539611613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-30800844376574844866657938788931625000000000)
      constant := (905788621591936816409168009499371115370104793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54253497883958227743/10000000000000000000)
  centralHi := (542534978839582277431/100000000000000000000)
  directionLo := (544829005895439006297/100000000000000000000)
  directionHi := (272414502947719503149/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree120.table
  base := (43577995442379325874980452810250248217297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-15485333380600864651311515711953000000000000)
      constant := (458154419807058745589163985589988464606444217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree120.table
  base := (87155990884655505388137728353889591710339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-31059812369929752628588959316281000000000000)
      constant := (921410030332100936421579211319969455107432379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544829005895439006297/100000000000000000000)
  centralHi := (272414502947719503149/50000000000000000000)
  directionLo := (54711341426212411359/10000000000000000000)
  directionHi := (547113414262124113591/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree121.table
  base := (44760236904476042627390526097821508856461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-140530013435177565915769511484685125000000000)
      constant := (4193906147781789020667764276782886201415266789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree121.table
  base := (44760236904433963946344639323693463764053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-15659390181642330195259989921815187500000000)
      constant := (468582865678031495909559822834159292078979383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54711341426212411359/10000000000000000000)
  centralHi := (547113414262124113591/100000000000000000000)
  directionLo := (137347080981473937223/25000000000000000000)
  directionHi := (549388323925895748893/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree122.table
  base := (91914204376060958983752365221747535274549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-283384052889894699939470763123586500000000000)
      constant := (8530047285307599723782986915408523320232009701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree122.table
  base := (18382840875198459895792937936066336127499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-6315549671327913630490200074195950000000000)
      constant := (190611144932819831346256479230035788748277139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137347080981473937223/25000000000000000000)
  centralHi := (549388323925895748893/100000000000000000000)
  directionLo := (551653852398994198591/100000000000000000000)
  directionHi := (8619591443734284353/1562500000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree123.table
  base := (94337182586828206965913223079466928272627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-31745342101048252005266944808644750000000000)
      constant := (963720502862392917845296946389642924387668347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree123.table
  base := (47168591293386097548975985861414841598361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-15918358174997237957191010449164562500000000)
      constant := (484540005128238930857687067236529369633414571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551653852398994198591/100000000000000000000)
  centralHi := (8619591443734284353/1562500000000000000)
  directionLo := (553910114790475368207/100000000000000000000)
  directionHi := (34619382174404710513/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree124.table
  base := (19357881688395189973662834791782506494807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-57606420985794767231066848686403800000000000)
      constant := (1763624803385546764371366518186046626101627943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree124.table
  base := (96789408441930258858594665576286936568993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-32095684343349383676313041425678500000000000)
      constant := (985238588133459981294723478866265537226406473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553910114790475368207/100000000000000000000)
  centralHi := (34619382174404710513/6250000000000000000)
  directionLo := (556157223874457933131/100000000000000000000)
  directionHi := (139039305968614483283/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree125.table
  base := (49635440971103012118689657367473731781973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-145178065474256702131632991793117625000000000)
      constant := (4481982879404236337234899513212647008075255277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree125.table
  base := (99270881942168754766630935085765411149443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-32354652336704291438244061953027875000000000)
      constant := (1001531458295299032775401906477866708932761423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556157223874457933131/100000000000000000000)
  centralHi := (139039305968614483283/25000000000000000000)
  directionLo := (279197645077949324719/50000000000000000000)
  directionHi := (558395290155898649439/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree126.table
  base := (101781603088200535189844406270298041532469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-32520017440894774707910858193383500000000000)
      constant := (1012334416822885441996760701226107421118221309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree126.table
  base := (6361350193010633561653986181102946236513/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-16306810165029599600087541240188625000000000)
      constant := (508979310371120691055379449909603084121674544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279197645077949324719/50000000000000000000)
  centralHi := (558395290155898649439/100000000000000000000)
  directionLo := (112124884386800874881/20000000000000000000)
  directionHi := (280312210967002187203/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree127.table
  base := (20864314376124484530728036461395292386893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-59000836597518508095825892778933550000000000)
      constant := (1851851198944475324837164279737409815121265357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree127.table
  base := (104321571880597630442178742548698381245247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-32872588323414106962106103007726625000000000)
      constant := (1034520075474526453498389340829056534574846667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112124884386800874881/20000000000000000000)
  centralHi := (280312210967002187203/50000000000000000000)
  directionLo := (281422362681691878657/50000000000000000000)
  directionHi := (112568945072676751463/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree128.table
  base := (6680674270007252088927428128384462264493/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-148664104503566054293530602024442000000000000)
      constant := (4704352244379894547924332445302064943178702056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree128.table
  base := (21378157664019162921478559967601368626391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-6626311263353802944807424707015200000000000)
      constant := (210243164498477388025653791409777694074127151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281422362681691878657/50000000000000000000)
  centralHi := (112568945072676751463/20000000000000000000)
  directionLo := (565056304513036301533/100000000000000000000)
  directionHi := (282528152256518150767/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree129.table
  base := (21897850481461538605209345081146204453177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-6658938556148259482110954315624450000000000)
      constant := (212430116300449807213373749047233708713846897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree129.table
  base := (109489252407291204962321253367450008177281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-33390524310123922485968144062425375000000000)
      constant := (1068045861796049014088755472717979746897310941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565056304513036301533/100000000000000000000)
  centralHi := (282528152256518150767/50000000000000000000)
  directionLo := (35453703838954471679/6250000000000000000)
  directionHi := (113451852284654309373/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree130.table
  base := (112116964142806272797116309294622998235869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-301976261046211244802924684357316500000000000)
      constant := (9711208229005711533408969623782227074393338381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree130.table
  base := (112116964142792827898724350801755274874027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-33649492303478830247899164589774750000000000)
      constant := (1085010193385732533907274337243296955010773747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35453703838954471679/6250000000000000000)
  centralHi := (113451852284654309373/20000000000000000000)
  directionLo := (569453696160646456539/100000000000000000000)
  directionHi := (28472684808032322827/5000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree131.table
  base := (114773923527203748647638591999683215541387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-304300287065750812910856424511532750000000000)
      constant := (9864263475218123052006876767990263224325216363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree131.table
  base := (28693480881798196473152604530210222832201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-16954230148416869004915092558562062500000000)
      constant := (551054408630825624288832278151795291138755372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569453696160646456539/100000000000000000000)
  centralHi := (28472684808032322827/5000000000000000000)
  directionLo := (1429099267177511743/250000000000000000)
  directionHi := (571639706871004697201/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree132.table
  base := (29365032640268937231604722808946186055607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-17034684060293910056599342481430500000000000)
      constant := (556584498453297005383378256500291552582148254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree132.table
  base := (367062908003333783099734271664468210363/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-3416742829018864577176120564447350000000000)
      constant := (111934173342401299722483084958932082078613376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1429099267177511743/250000000000000000)
  centralHi := (571639706871004697201/100000000000000000000)
  directionLo := (17931793432209292357/3125000000000000000)
  directionHi := (22952695593227894217/4000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree133.table
  base := (2403511704899641789114569489414823570841/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (675629876675545207320716658000000000000)
      linear := (-85581257369758988677761746487525000000000)
      constant := (2818277207709473548392610670036040888812845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree133.table
  base := (120175585244974802123184853548286052627393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (140)
      previous := (70)
      next := (70)
      square := (750699862972828008134129620000000000000)
      linear := (-95363978624774386519923064187875000000000)
      constant := (3148778232335235190566361862129689372939893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17931793432209292357/3125000000000000000)
  centralHi := (22952695593227894217/4000000000000000000)
  directionLo := (575986839496060724633/100000000000000000000)
  directionHi := (287993419748030362317/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree134.table
  base := (122920287579467294392865321224102942001769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-311272365124369517234651644974181500000000000)
      constant := (10330642718235452449383485608923861536688747481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree134.table
  base := (76825179737163345900595098939396441681/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-3468536427689846129562324669917225000000000)
      constant := (115421044260886856634312798522309784174619560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575986839496060724633/100000000000000000000)
  centralHi := (287993419748030362317/50000000000000000000)
  directionLo := (578148148551223106533/100000000000000000000)
  directionHi := (289074074275611553267/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree135.table
  base := (12569423756506110200697307088724699599981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-3484404346043434281584259834759975000000000)
      constant := (116538966304153622617730439685212149758718141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree135.table
  base := (62847118782528129476464151823363643828337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-17472166135126684528777133613260812500000000)
      constant := (585923117815875120326014366038278789582185907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578148148551223106533/100000000000000000000)
  centralHi := (289074074275611553267/50000000000000000000)
  directionLo := (580301407954309087771/100000000000000000000)
  directionHi := (145075351988577271943/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree136.table
  base := (12849743520227895480819369410103479500587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-31592041716344865345051512528261400000000000)
      constant := (1064757346724799494104953766967796229897407163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree136.table
  base := (64248717601137503487564418540585871360881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-17601650131804138409742643876935500000000000)
      constant := (594808160470925509001620242718674655811278041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580301407954309087771/100000000000000000000)
  centralHi := (145075351988577271943/25000000000000000000)
  directionLo := (582446706982106462101/100000000000000000000)
  directionHi := (291223353491053231051/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree137.table
  base := (65664940245811236868833128887600555873291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-159122221591494110779223432718415125000000000)
      constant := (5403921108929794466091320365670098137672947459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree137.table
  base := (131329880491619255821094525565140744276401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-35462268256963184581416308281220375000000000)
      constant := (1207520698539351997047951462177590118254093261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582446706982106462101/100000000000000000000)
  centralHi := (291223353491053231051/50000000000000000000)
  directionLo := (292292066636628929603/50000000000000000000)
  directionHi := (584584133273257859207/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree138.table
  base := (5367662937343196653505708374496581437313/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-7123743760056173103697302346467700000000000)
      constant := (243762515982448763505551674087322570119349965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree138.table
  base := (134191573433577293522649886534255368319309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-35721236250318092343347328808569750000000000)
      constant := (1225559368424429449765650313091539207494520549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292292066636628929603/50000000000000000000)
  centralHi := (584584133273257859207/100000000000000000000)
  directionLo := (586713772870036201981/100000000000000000000)
  directionHi := (293356886435018100991/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree139.table
  base := (68541257014313309491591470542967082629339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-161446247611033678887155172872631375000000000)
      constant := (5565993235650677792816830533639644623728347411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree139.table
  base := (68541257014312240663768898424778083612271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-17990102121836500052639174667959562500000000)
      constant := (621866165298627490783386108363016109375436081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586713772870036201981/100000000000000000000)
  centralHi := (293356886435018100991/50000000000000000000)
  directionLo := (117767142051752066857/20000000000000000000)
  directionHi := (294417855129380167143/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree140.table
  base := (140002702277225423380281086879496113783451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-325216521241606925882242085899479000000000000)
      constant := (11295861974134576388536922872540225686182432299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree140.table
  base := (14000270227722368123097340815306217717941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-3623917223702790786720936986326850000000000)
      constant := (126203958505799568563158984282383802408676701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117767142051752066857/20000000000000000000)
  centralHi := (294417855129380167143/50000000000000000000)
  directionLo := (590950028408904531063/100000000000000000000)
  directionHi := (73868753551113066383/12500000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree141.table
  base := (71476069089913543813866838219961269771751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-18196697070063694110565212558538625000000000)
      constant := (636718873761740071084588926372072231278227111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree141.table
  base := (28590427635965133576213552679303704918217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-7299628046076563125828078078123575000000000)
      constant := (256096226361362858321614255578107322827038837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590950028408904531063/100000000000000000000)
  centralHi := (73868753551113066383/12500000000000000000)
  directionLo := (118611361762190622659/20000000000000000000)
  directionHi := (37066050550684569581/6250000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree142.table
  base := (72965410868435341103963299038011354680937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-164932286640343031049052783103955750000000000)
      constant := (5813609866016508399293983112432916992920864313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree142.table
  base := (36482705434217381314532787218741426449489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-18378554111868861695535705458983625000000000)
      constant := (649528485421934654406554267639318804037156058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118611361762190622659/20000000000000000000)
  centralHi := (37066050550684569581/6250000000000000000)
  directionLo := (297578065756524516487/50000000000000000000)
  directionHi := (23806245260521961319/4000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree143.table
  base := (148938752948783971320093210624929751370969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-332188599300225630206037306362127750000000000)
      constant := (11794701987101052751616328705907672687985528281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree143.table
  base := (74469376474391514284930818741902444045751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-18508038108546315576501215722658312500000000)
      constant := (658883551084657582048340309651690413648172361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297578065756524516487/50000000000000000000)
  centralHi := (23806245260521961319/4000000000000000000)
  directionLo := (14931201878912076509/2500000000000000000)
  directionHi := (597248075156483060361/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree144.table
  base := (4749247869249493125080695801393697785071/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-18584034739986955461887169250908000000000000)
      constant := (664632582939821300175404622868589498406570096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree144.table
  base := (18996991476997876479024640158872184810611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-18637522105223769457466725986333000000000000)
      constant := (668305762891651167269270554497036559866522284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14931201878912076509/2500000000000000000)
  centralHi := (597248075156483060361/100000000000000000000)
  directionLo := (5993327170100680897/1000000000000000000)
  directionHi := (599332717010068089701/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree145.table
  base := (155042358338876347511566405883460848360841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-336836651339304766421900786670560250000000000)
      constant := (12133273249481528624554134658336305722105622409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree145.table
  base := (155042358338875721622241378567346719833271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-37534012203802446676864472500015375000000000)
      constant := (1355590241685977475153024468328156116055123331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5993327170100680897/1000000000000000000)
  centralHi := (599332717010068089701/100000000000000000000)
  directionLo := (300705066501720536797/50000000000000000000)
  directionHi := (120282026600688214719/20000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree146.table
  base := (39534508129464416858765821673493830527627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-169580338679422167264916263412388250000000000)
      constant := (6152181128398287499487176204126446512331020246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree146.table
  base := (158138032517857157497635661363831824551807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-37792980197157354438795493027364750000000000)
      constant := (1374703249877483541780439189274351651944452327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300705066501720536797/50000000000000000000)
  centralHi := (120282026600688214719/20000000000000000000)
  directionLo := (301740198879666596869/50000000000000000000)
  directionHi := (603480397759333193739/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree147.table
  base := (161262954353313815025249666574663547291473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-37942744819820433626418251886554750000000000)
      constant := (1386294834984797431656917638860674466353471753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree147.table
  base := (161262954353313399578012382557057265225687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-38051948190512262200726513554714125000000000)
      constant := (1393950550357959909343972572888341162004285507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301740198879666596869/50000000000000000000)
  centralHi := (603480397759333193739/100000000000000000000)
  directionLo := (605543584624847070921/100000000000000000000)
  directionHi := (302771792312423535461/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree148.table
  base := (82208561922810631115258998109669427741491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-171904364698961735372848003566604500000000000)
      constant := (6325073511841278719864090377560018376982104259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree148.table
  base := (164417123845620923780314167087656713879817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-38310916183867169962657534082063500000000000)
      constant := (1413332143127542485649640906773693401835613937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605543584624847070921/100000000000000000000)
  centralHi := (302771792312423535461/50000000000000000000)
  directionLo := (607599765701778104209/100000000000000000000)
  directionHi := (60759976570177810421/10000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree149.table
  base := (83800270497573590451453684680940113165007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-173066377708731519426813873643712625000000000)
      constant := (6412421391627954802384696719958082749938732743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree149.table
  base := (83800270497573452596023439388997829182819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-19284942088611038862294277304706437500000000)
      constant := (716424014093181910452016903885141156276403909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607599765701778104209/100000000000000000000)
  centralHi := (60759976570177810421/10000000000000000000)
  directionLo := (609649011876015402959/100000000000000000000)
  directionHi := (7620612648450192537/1250000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree150.table
  base := (170813205802249734647513094884346639497659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-38717420159666956329062165271293500000000000)
      constant := (1444526754842710783732094606965807339983654899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree150.table
  base := (170813205802249510055958332883855441495957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-38828852170576985486519575136762250000000000)
      constant := (1452498205534553213120783237185444958911290477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609649011876015402959/100000000000000000000)
  centralHi := (7620612648450192537/1250000000000000000)
  directionLo := (611691392846056230807/100000000000000000000)
  directionHi := (76461424105757028851/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree151.table
  base := (87027559133639179884548499108136413602169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-175390403728271087534745613797928875000000000)
      constant := (6588920527334577552370362997134448389434072081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree151.table
  base := (174055118267278176826987025539612626701527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-39087820163931893248450595664111625000000000)
      constant := (1472282675172236809582121992123691280309563747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611691392846056230807/100000000000000000000)
  centralHi := (76461424105757028851/12500000000000000000)
  directionLo := (613726977150666413271/100000000000000000000)
  directionHi := (76715872143833301659/12500000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree152.table
  base := (17732627839057403575806106847807552506447/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (675629876675545207320716658000000000000)
      linear := (-97812973262072505035297220983400000000000)
      constant := (3699762760806451966922252935539692972558023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree152.table
  base := (177326278390573886748232564094584772327571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (140)
      previous := (70)
      next := (70)
      square := (750699862972828008134129620000000000000)
      linear := (-108993873011874795042608355101000000000000)
      constant := (4133521986425312200877587343041897272327571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613726977150666413271/100000000000000000000)
  centralHi := (76715872143833301659/12500000000000000000)
  directionLo := (615755832195717765961/100000000000000000000)
  directionHi := (307877916097858882981/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree153.table
  base := (90313343086234772871872002643838083934379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-19746047749756739515853039328016125000000000)
      constant := (751980462728438208528994122602170964315935819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree153.table
  base := (36125337234493884875530567654674567390099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-7921151230128341754462527343762075000000000)
      constant := (302450898263315206630053430303865361991888239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615755832195717765961/100000000000000000000)
  centralHi := (307877916097858882981/50000000000000000000)
  directionLo := (38611126517514517153/6250000000000000000)
  directionHi := (617778024280232274449/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree154.table
  base := (183956341613289727328072709459018317964911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-357752885515160879393286448058506500000000000)
      constant := (13716355342471998960907069823635756593192995839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree154.table
  base := (9197817080664481424078836286577584198911/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-3986472414399661653424365724615975000000000)
      constant := (153244183782346906227714107900095948994738742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38611126517514517153/6250000000000000000)
  centralHi := (617778024280232274449/100000000000000000000)
  directionLo := (123958723724332299139/20000000000000000000)
  directionHi := (38737101163853843481/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree155.table
  base := (2341440558916896427465944014273778053961/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-36007691153470044750121818821272275000000000)
      constant := (1389826460659265559009141582483503041131679312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree155.table
  base := (187315244713351633695233615050738287941543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-40123692137351524296174677773509125000000000)
      constant := (1552763476620331277500748622560986683079709523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123958723724332299139/20000000000000000000)
  centralHi := (38737101163853843481/6250000000000000000)
  directionLo := (155450669845107112823/25000000000000000000)
  directionHi := (621802679380428451293/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree156.table
  base := (38140679094593033778778793081174949704651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-8053354167872000346869998408154200000000000)
      constant := (312919469366108082992792213897507919343379011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree156.table
  base := (190703395472965103334571996503845813206577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-40382660130706432058105698300858500000000000)
      constant := (1573219407707274467278147187187930041692574297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155450669845107112823/25000000000000000000)
  centralHi := (621802679380428451293/100000000000000000000)
  directionLo := (9746957338808720951/1562500000000000000)
  directionHi := (124761053936751628173/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree157.table
  base := (194120793892432507115909224770889359318177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-364724963573779583717081668521155250000000000)
      constant := (14265689887119605943262512087301563485456007073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree157.table
  base := (7764831755697298149113767182916209729191/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722000000000000000000000000000000000000000
      center := (10108)
      previous := (5054)
      next := (5054)
      square := (54200530106638182187284158564000000000000)
      linear := (-8128325624812267964007343765641575000000000)
      constant := (318761926216881560780767171320960550162752255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9746957338808720951/1562500000000000000)
  centralHi := (124761053936751628173/20000000000000000000)
  directionLo := (625801451648821717079/100000000000000000000)
  directionHi := (15645036291220542927/2500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree158.table
  base := (19756743997204911389457529684143091321697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-36704898959331915182501340867537150000000000)
      constant := (1445120590352784192181854744879312299016693553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree158.table
  base := (197567439972049070419904148411898274886967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-40900596117416247581967739355557250000000000)
      constant := (1614534146751837921559506919091192203015445087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625801451648821717079/100000000000000000000)
  centralHi := (15645036291220542927/2500000000000000000)
  directionLo := (627791286405218328547/100000000000000000000)
  directionHi := (156947821601304582137/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree159.table
  base := (201043333712103551987632752975329431870269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-41041446179206524436993905425509750000000000)
      constant := (1626436018966723245638183869578236069436417109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree159.table
  base := (201043333712103516586997962759270491072351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-41159564110771155343898759882906625000000000)
      constant := (1635392954709668991551785202212677253722431211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627791286405218328547/100000000000000000000)
  centralHi := (156947821601304582137/25000000000000000000)
  directionLo := (314887417058408825397/50000000000000000000)
  directionHi := (125954966823363530159/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree160.table
  base := (399508740454839380488369316569976382431/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (227430)
      previous := (113715)
      next := (113715)
      square := (1219511927399359099213893567690000000000000)
      linear := (-185848520816199144020438444491902000000000000)
      constant := (7412922344319261918847525310499598436228689664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree160.table
  base := (12784279694554858374068158015451787148379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-20709266052063031552914890205128000000000000)
      constant := (828193027479001397427287018451242261284518552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314887417058408825397/50000000000000000000)
  centralHi := (125954966823363530159/20000000000000000000)
  directionLo := (631752154002985185891/100000000000000000000)
  directionHi := (157938038500746296473/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree161.table
  base := (208082864174647260210310482273069057851079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-374021067651937856148808629138020250000000000)
      constant := (15014967457342780947166505400849197419739405671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree161.table
  base := (130051790109154522962823241193814233217/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-4167750009748097086776080093760537500000000)
      constant := (167751344749693879206748048127400720755145170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631752154002985185891/100000000000000000000)
  centralHi := (157938038500746296473/25000000000000000000)
  directionLo := (316861652179605757819/50000000000000000000)
  directionHi := (633723304359211515639/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree162.table
  base := (211646500897681317386793546353891335188307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-41816121519053047139637818810248500000000000)
      constant := (1689476941868239489753278422863615600127978827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree162.table
  base := (211646500897681298278004775563694563499743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-41936468090835878629691821464954750000000000)
      constant := (1698775132326574190896830924500749663204657223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316861652179605757819/50000000000000000000)
  centralHi := (633723304359211515639/100000000000000000000)
  directionLo := (79461042822145729903/12500000000000000000)
  directionHi := (25427533703086633569/4000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree163.table
  base := (43047877056448629445083637549261951884147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6498000000000000000000000000000000000000000
      center := (90972)
      previous := (45486)
      next := (45486)
      square := (487804770959743639685557427076000000000000)
      linear := (-75733823938203398472934421889290550000000000)
      constant := (3079363949410700479640083720895770923077843603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree163.table
  base := (21523938528224313166789264248407131789403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-4219543608419078639162284199230412500000000)
      constant := (172017110944700401126101787022737220376755733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79461042822145729903/12500000000000000000)
  centralHi := (25427533703086633569/4000000000000000000)
  directionLo := (637647325164193311751/100000000000000000000)
  directionHi := (79705915645524163969/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree164.table
  base := (218861517328590076327476296927651858728519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-380993145710556560472603849600669000000000000)
      constant := (15589549268061657972556841149128977201508958231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree164.table
  base := (10943075866429503183085374874788627108687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361000000000000000000000000000000000000000
      center := (5054)
      previous := (2527)
      next := (2527)
      square := (27100265053319091093642079282000000000000)
      linear := (-4245440407754569415355386251965350000000000)
      constant := (174170137885832114811734246106153359084972014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637647325164193311751/100000000000000000000)
  centralHi := (79705915645524163969/12500000000000000000)
  directionLo := (319800153881137461459/50000000000000000000)
  directionHi := (639600307762274922919/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree165.table
  base := (111256448518486856492120915623294274341933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-21295398429449784921140866097493625000000000)
      constant := (876860057768857755899284584841596664678062813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree165.table
  base := (111256448518486851336553584936626129842581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-21356686035450300957742441523501437500000000)
      constant := (881682970280308216051567586685655863439577991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319800153881137461459/50000000000000000000)
  centralHi := (639600307762274922919/100000000000000000000)
  directionLo := (12830946903329358271/2000000000000000000)
  directionHi := (641547345166467913551/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree166.table
  base := (226193524407640109343532942535641099070281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-385641197749635696688467329909101500000000000)
      constant := (15978615062387646722519523913842004509004342969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree166.table
  base := (226193524407640100949601351210405485098041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-42972340064255509677415903574352250000000000)
      constant := (1785164794553978688079747005822102712151642801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12830946903329358271/2000000000000000000)
  centralHi := (641547345166467913551/100000000000000000000)
  directionLo := (643488491342844019713/100000000000000000000)
  directionHi := (321744245671422009857/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree167.table
  base := (22990339944082991800232855450059862373799/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (45486)
      previous := (22743)
      next := (22743)
      square := (243902385479871819842778713538000000000000)
      linear := (-38796522376917526479639907006331775000000000)
      constant := (1617495133570706120184162983232887966680597951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree167.table
  base := (229903399440829911169372176579103108122247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-43231308057610417439346924101701625000000000)
      constant := (1807097940838494791664001709174851937852443667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643488491342844019713/100000000000000000000)
  centralHi := (321744245671422009857/50000000000000000000)
  directionLo := (161355949861485539529/25000000000000000000)
  directionHi := (645423799445942158117/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree168.table
  base := (233642522136778543249008751943760921759521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-43365472198746092544925645579726000000000000)
      constant := (1819165539977605319187376353125781942755187081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree168.table
  base := (233642522136778537686940485341792783375997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (50540)
      previous := (25270)
      next := (25270)
      square := (271002650533190910936420792820000000000000)
      linear := (-43490276050965325201277944629051000000000000)
      constant := (1829165379414249723827881306439403007298734917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell036.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161355949861485539529/25000000000000000000)
  centralHi := (645423799445942158117/100000000000000000000)
  directionLo := (647353321835751520843/100000000000000000000)
  directionHi := (161838330458937880211/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree169.table
  base := (237410892495716287168736406033012029458121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (454860)
      previous := (227430)
      next := (227430)
      square := (2439023854798718198427787135380000000000000)
      linear := (-392613275808254401012262550371750250000000000)
      constant := (16571230634662554986528490119675933196990685129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree169.table
  base := (118705446247858141320669537004131586267139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (25270)
      previous := (12635)
      next := (12635)
      square := (135501325266595455468210396410000000000000)
      linear := (-21874622022160116481604482578200187500000000)
      constant := (925683555140663311821788318577894813677593429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell036.Kernel169
