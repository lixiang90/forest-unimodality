import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell057.Parameters
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch000_049
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch050_099
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch100_149
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch150_199
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch000_049
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch050_099
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch100_149
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree000.table
  base := (709282885725091249329210549/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (729240441294997515653264490000000000000)
      linear := (12026166872766506227288019000000000000)
      constant := (709282885725091249329210549000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree000.table
  base := (709282885725091249329210549/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (729240441294997515653264490000000000000)
      linear := (12026166872766506227288019000000000000)
      constant := (709282885725091249329210549000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree001.table
  base := (8106616634749053337399246854167974052953/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-5523877596780214377401811048099012000000000000)
      constant := (3180775383142132798894362793679570146406243992550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree001.table
  base := (404536730923136086217639335732388601637549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-5538617369199889514686952656603137000000000000)
      constant := (3174553529576753581711379284312832643281244071783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24996025209852469769/50000000000000000000)
  directionHi := (49992050419704939539/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree002.table
  base := (24279374080778062202048120278505099013349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-11142089252263589705006386545531297000000000000)
      constant := (1909915749340905586643714987438715339023434503830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree002.table
  base := (120974188742137716253640105574023816256107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-11171568797102939979576669762539547000000000000)
      constant := (1903313411578384523706443595608917847617184934338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/50000000000000000000)
  centralHi := (49992050419704939539/100000000000000000000)
  directionLo := (8837429464298288003/12500000000000000000)
  directionHi := (2827977428575452161/4000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree003.table
  base := (76852913638040268111869155907229360573159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-1862255656416329448067884671440398000000000000)
      constant := (135328377750293445584665757778031591003448355034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree003.table
  base := (15301569328200744442999932364582438333793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-622389637963184831276532846980591000000000000)
      constant := (44911363316397008470238931126797758671718761530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/12500000000000000000)
  centralHi := (2827977428575452161/4000000000000000000)
  directionLo := (86588771301473971569/100000000000000000000)
  directionHi := (8658877130147397157/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree004.table
  base := (51585212917466129235239365580784503628249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-22378512563230340360215537540395867000000000000)
      constant := (831162553629359808082479932636033681043456497366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree004.table
  base := (102654074871022768446316824632094138277077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-22437471652909040909356103974412367000000000000)
      constant := (827227743376320291791034841238449508952656552159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86588771301473971569/100000000000000000000)
  centralHi := (8658877130147397157/10000000000000000000)
  directionLo := (24996025209852469769/25000000000000000000)
  directionHi := (99984100839409879077/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree005.table
  base := (73200905249130567522808862081551264011227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-27996724218713715687820113037828152000000000000)
      constant := (608448870457819465965318997914396416963753340209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree005.table
  base := (36412066273511848104869284370477483961899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-28070423080812091374245821080348777000000000000)
      constant := (605674031599566300773835406695773672377122406466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/25000000000000000000)
  centralHi := (99984100839409879077/100000000000000000000)
  directionLo := (111785623073057136791/100000000000000000000)
  directionHi := (13973202884132142099/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree006.table
  base := (13610575232270079084678779213258658466109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-1244997624970262630200914390194831000000000000)
      constant := (17645680785726227690300096994094895864929811156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree006.table
  base := (54165621775279109555613956028401854868759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-3744819389857237982126170909587243000000000000)
      constant := (52724809882849170864046277693837818834980200317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111785623073057136791/100000000000000000000)
  centralHi := (13973202884132142099/12500000000000000000)
  directionLo := (122455014723766723037/100000000000000000000)
  directionHi := (61227507361883361519/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree007.table
  base := (41992416332850502618653826989053875953721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-800676480197560537612842123116178000000000000)
      constant := (8095161791380627789511350824020143249299518843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree007.table
  base := (41784468215302560376187503726989988907701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-802782161971799842939290924331053000000000000)
      constant := (8069103436424336556112671274276879394311499183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122455014723766723037/100000000000000000000)
  centralHi := (61227507361883361519/50000000000000000000)
  directionLo := (16533316617592682509/12500000000000000000)
  directionHi := (132266532940741460073/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree008.table
  base := (33239946105734134860715105383306082311349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-44851359185163841670633839530125007000000000000)
      constant := (348654255987166901399767930099394777157736416383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree008.table
  base := (16539447581143091330309957927765324127853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-44969277364521242768914972398158007000000000000)
      constant := (347853859125464038077102422371578761471190996302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16533316617592682509/12500000000000000000)
  centralHi := (132266532940741460073/100000000000000000000)
  directionLo := (8837429464298288003/6250000000000000000)
  directionHi := (141398871428772608049/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree009.table
  base := (13381357836600293111586949505474662897677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-1869243364468415444379200556576196000000000000)
      constant := (11898212340549697640027708388976767454392039434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree009.table
  base := (5326852130369674478332832871035641312539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-1874156621941640490140914426077571000000000000)
      constant := (11882596845112454177052083162818901748800714095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/6250000000000000000)
  centralHi := (141398871428772608049/100000000000000000000)
  directionLo := (74988075629557409307/50000000000000000000)
  directionHi := (29995230251822963723/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree010.table
  base := (680075320057939602792699052447041817673/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-56087782496130592325842990524989577000000000000)
      constant := (308193324674187836626794716317549539028121474912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree010.table
  base := (21657416798751697031351732308490792070323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-56235180220327343698694406610030827000000000000)
      constant := (308093330309798433623627270922114336882682323641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/50000000000000000000)
  centralHi := (29995230251822963723/20000000000000000000)
  directionLo := (158088744228244182147/100000000000000000000)
  directionHi := (39522186057061045537/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree011.table
  base := (444325717881371439566164305136913874377/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-509966893814991468210310462995222000000000000)
      constant := (2527468484319489864114255952689931254369511160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree011.table
  base := (1768565906647060792939367534286555193869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-511306873125871026145323336495597000000000000)
      constant := (2529041489380497518860656611005132135529456630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158088744228244182147/100000000000000000000)
  centralHi := (39522186057061045537/25000000000000000000)
  directionLo := (165804873742690474133/100000000000000000000)
  directionHi := (82902436871345237067/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree012.table
  base := (1813688727700375356453172730015984005393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-7480467311899704775672460168872683000000000000)
      constant := (34656308807238788369889750083054909541538714072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree012.table
  base := (14435945394344436341859381221123956196599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-2500040113930868319573105215626061000000000000)
      constant := (11569332727634118939397970988340074878192138079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165804873742690474133/100000000000000000000)
  centralHi := (82902436871345237067/50000000000000000000)
  directionLo := (86588771301473971569/50000000000000000000)
  directionHi := (173177542602947943139/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree013.table
  base := (2947082466629993455667962276679792563309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-72942417462580718308656717017286432000000000000)
      constant := (325003030506867594956520556773835495775790150812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree013.table
  base := (11725964269780788553905314450261226265083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-73134034504036495093363557927840057000000000000)
      constant := (325737156883395388378832984258789922325470812561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86588771301473971569/50000000000000000000)
  centralHi := (173177542602947943139/100000000000000000000)
  directionLo := (18024890115382720601/10000000000000000000)
  directionHi := (180248901153827206011/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree014.table
  base := (296412957942150600682291755854429394209/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-1603278145266614155842067194177933000000000000)
      constant := (7023216841002871923096806989471344862821099104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree014.table
  base := (1179021031778855162990398809345715059211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-1607489508815092766494964796607683000000000000)
      constant := (7043682153902191395758955935590737830589396104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18024890115382720601/10000000000000000000)
  centralHi := (180248901153827206011/100000000000000000000)
  directionLo := (187053124732864303733/100000000000000000000)
  directionHi := (93526562366432151867/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree015.table
  base := (1502423870743172304358227735866318458393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-3117734843464721072735772889338926000000000000)
      constant := (13652590141495410918296091118169780399253963765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree015.table
  base := (7466956919300137373642892709353870122879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-9377770817760288447015888015523653000000000000)
      constant := (41099405110000261839452040871986132105906789877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187053124732864303733/100000000000000000000)
  centralHi := (93526562366432151867/50000000000000000000)
  directionLo := (96809189359139368223/50000000000000000000)
  directionHi := (193618378718278736447/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree016.table
  base := (5804314035544908228592470741117077766451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-89797052429030844291470443509583287000000000000)
      constant := (397942210435288364415810562915360624844251996217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree016.table
  base := (2882942046163260788198657235185703672643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-90032888787745646488032709245649287000000000000)
      constant := (399494298133524809218857273747845146100715518162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96809189359139368223/50000000000000000000)
  centralHi := (193618378718278736447/100000000000000000000)
  directionLo := (24996025209852469769/12500000000000000000)
  directionHi := (199968201678819758153/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree017.table
  base := (86257008798524385193821165810407997791/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-95415264084514219619075019007015572000000000000)
      constant := (431720501625180931337113346157459413725422799850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree017.table
  base := (4280194785506402515614508159480771770519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-95665840215648696952922426351585697000000000000)
      constant := (433556944580859182628221631262007112979659660773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/12500000000000000000)
  centralHi := (199968201678819758153/100000000000000000000)
  directionLo := (103061252160823582199/50000000000000000000)
  directionHi := (206122504321647164399/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree018.table
  base := (749989368014166536257968084940497429809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-3741980582962873886914059055720291000000000000)
      constant := (17394760310805729778858654401844271015222161956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree018.table
  base := (743064964741459953577000815829185876353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-3751807097909323978437486794723041000000000000)
      constant := (17473608142136367293039789169999996639935799652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103061252160823582199/50000000000000000000)
  centralHi := (206122504321647164399/100000000000000000000)
  directionLo := (26512288392894864009/12500000000000000000)
  directionHi := (212098307143158912073/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree019.table
  base := (459019817564825007088323640096026828927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-106651687395480970274284170001880142000000000000)
      constant := (511524452575772963307932027295517817144603704436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree019.table
  base := (453158837918337364148423822594626159611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-106931743071454797882701860563458517000000000000)
      constant := (513954763500916662340391322865490188743765511748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512288392894864009/12500000000000000000)
  centralHi := (212098307143158912073/100000000000000000000)
  directionLo := (27238786969985493351/12500000000000000000)
  directionHi := (217910295759883946809/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree020.table
  base := (797871080146027583027894914076073171519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-112269899050964345601888745499312427000000000000)
      constant := (557135156359716961117039976236305376054297527773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree020.table
  base := (778069622846609102773732700702647175803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-112564694499357848347591577669394927000000000000)
      constant := (559876588142406950064985969852951801524359510801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27238786969985493351/12500000000000000000)
  centralHi := (217910295759883946809/100000000000000000000)
  directionLo := (223571246146114273583/100000000000000000000)
  directionHi := (13973202884132142099/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree021.table
  base := (-133219669959019750545622198292718478879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2525754)
      previous := (1262877)
      next := (1262877)
      square := (12970999729314120810924615483630000000000000)
      linear := (-267319978926185308230143585026632000000000000)
      constant := (1374932227048387487963268616112862541416179227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree021.table
  base := (-468467819536850004242744291997084129/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-89340624283643914446319950699419000000000000)
      constant := (460625846724915663434125072739643772223730880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223571246146114273583/100000000000000000000)
  centralHi := (13973202884132142099/6250000000000000000)
  directionLo := (229092355194346756381/100000000000000000000)
  directionHi := (114546177597173378191/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree022.table
  base := (-971996008728675596887680314622016274439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-1020713407949843770719817326398157000000000000)
      constant := (5446596726718397508277896137225257550976942947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree022.table
  base := (-493017656302208247928436468933090927093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-1023393366571602886589843073398907000000000000)
      constant := (5474656367978650389546917741683858028938684178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229092355194346756381/100000000000000000000)
  centralHi := (114546177597173378191/50000000000000000000)
  directionLo := (58620875288617886087/25000000000000000000)
  directionHi := (234483501154471544349/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree023.table
  base := (-54071861125840099553859347843745813789/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-129124534017414471584702471991609282000000000000)
      constant := (715121545313877308468350880045922455406425924384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree023.table
  base := (-87104334470459582438703167890081266419/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-129463548783066999742260728987204157000000000000)
      constant := (718860465027724991548761875929949219215290278540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58620875288617886087/25000000000000000000)
  centralHi := (234483501154471544349/100000000000000000000)
  directionLo := (47950690263571964097/20000000000000000000)
  directionHi := (119876725658929910243/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree024.table
  base := (-483523705343663381414683073397435565437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-4990472061959179515270631388483021000000000000)
      constant := (28685952225114207786795338868147232110468386615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree024.table
  base := (-606874279377252167204565483497241288181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-15010722245663338911905605121460063000000000000)
      constant := (86512792600627842538808609025942867564596412388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47950690263571964097/20000000000000000000)
  centralHi := (119876725658929910243/50000000000000000000)
  directionLo := (9796401177901337843/4000000000000000000)
  directionHi := (61227507361883361519/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree025.table
  base := (-760390851872087380289886528802292964517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-140360957328381222239911622986473852000000000000)
      constant := (837176001058082331975838019430017165055800117444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree025.table
  base := (-381228582809606740874164263451752674017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-140729451638873100672040163199076977000000000000)
      constant := (841638108310180572552482841756050456060651942888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9796401177901337843/4000000000000000000)
  centralHi := (61227507361883361519/25000000000000000000)
  directionLo := (24996025209852469769/10000000000000000000)
  directionHi := (249960252098524697691/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree026.table
  base := (-1804121313272534080265584729596721453129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-145979168983864597567516198483906137000000000000)
      constant := (903039503333744548255888071927226099882637528714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree026.table
  base := (-3615147258450681687211785083176477462501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-146362403066776151136929880305013387000000000000)
      constant := (907881808147519260169312113891678944960152168433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/10000000000000000000)
  centralHi := (249960252098524697691/100000000000000000000)
  directionLo := (254910440614589855517/100000000000000000000)
  directionHi := (127455220307294927759/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree027.table
  base := (-2061280541746627077025833125471417295953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-5614717801457332329448917554864386000000000000)
      constant := (36002694168294151141469293099332395626524876974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree027.table
  base := (-2064160350008129198068217823588618957587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-5629457573877007466734059163368511000000000000)
      constant := (36196594430029394683177432430595758663645734346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254910440614589855517/100000000000000000000)
  centralHi := (127455220307294927759/50000000000000000000)
  directionLo := (64941578476105478677/25000000000000000000)
  directionHi := (259766313904421914709/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree028.table
  base := (-573557291712757449323095215603173870733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-3208481475404721392300517336301443000000000000)
      constant := (21311118705151205937093331879312025938011593288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree028.table
  base := (-4593256307435314368898422440764546542293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-3216904202501678613606312541160943000000000000)
      constant := (21426248641185312066410175928134863095870109681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64941578476105478677/25000000000000000000)
  centralHi := (259766313904421914709/100000000000000000000)
  directionLo := (52906613176296584029/20000000000000000000)
  directionHi := (132266532940741460073/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree029.table
  base := (-5009099117158204957739218795970733271883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-162833803950314723550329924976202992000000000000)
      constant := (1119530900926652164028648115046777804301220531839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree029.table
  base := (-626636368994986712808886691640790850291/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-163261257350485302531599031622822617000000000000)
      constant := (1125591603741107756810622508980216661098643412024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52906613176296584029/20000000000000000000)
  centralHi := (132266532940741460073/50000000000000000000)
  directionLo := (67303857639172188009/25000000000000000000)
  directionHi := (269215430556688752037/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree030.table
  base := (-2693513009413537629974344478088497484609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-18716890622866455430881611163737253000000000000)
      constant := (133101227939983291933688201023013974733643452266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree030.table
  base := (-5390343233098539328432909247847778933601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-6255341065866235296166249952917001000000000000)
      constant := (44607576093206847232877203059106170416431303879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67303857639172188009/25000000000000000000)
  centralHi := (269215430556688752037/100000000000000000000)
  directionLo := (54763547421616004967/20000000000000000000)
  directionHi := (68454434277020006209/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree031.table
  base := (-5724281916088100474563342643185124074727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-174070227261281474205539075971067562000000000000)
      constant := (1279369243684964447908443393192273850979528405291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree031.table
  base := (-1431758867471223622915043788250866863997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-174527160206291403461378465834695437000000000000)
      constant := (1286309172538516373818377393737108167042910576804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54763547421616004967/20000000000000000000)
  centralHi := (68454434277020006209/25000000000000000000)
  directionLo := (55668791350326960539/20000000000000000000)
  directionHi := (34792994593954350337/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree032.table
  base := (-6022508258567587615812901982294384979349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-179688438916764849533143651468499847000000000000)
      constant := (1363892601961150748362208973259992214498192827617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree032.table
  base := (-6024791556884005840559411384370076872169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-180160111634194453926268182940631847000000000000)
      constant := (1371292719869133090634475055222059948219555928677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55668791350326960539/20000000000000000000)
  centralHi := (34792994593954350337/12500000000000000000)
  directionLo := (8837429464298288003/3125000000000000000)
  directionHi := (282797742857545216097/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree033.table
  base := (-3141511991988367313279166396184166620261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (340942)
      previous := (170471)
      next := (170471)
      square := (1750906299549289035083488040490000000000000)
      linear := (-56720737854988743452937932955596000000000000)
      constant := (444282454990092765672000906593941006889506678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree033.table
  base := (-6284915492020639173806310889969835346079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (1022826)
      previous := (511413)
      next := (511413)
      square := (5252718898647867105250464121470000000000000)
      linear := (-170608873335259416337151423366913000000000000)
      constant := (1340078023747791829065065950684121276002192963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/3125000000000000000)
  centralHi := (282797742857545216097/100000000000000000000)
  directionLo := (143591232732441386951/50000000000000000000)
  directionHi := (287182465464882773903/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree034.table
  base := (-6506888902361340276646578722253750785601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-190924862227731600188352802463364417000000000000)
      constant := (1542095465938404880553900353212734385836443120733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree034.table
  base := (-6508454410163375324941445792734203196279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-191426014490000554856047617152504667000000000000)
      constant := (1550457702719085823217314594005345919936773373307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143591232732441386951/50000000000000000000)
  centralHi := (287182465464882773903/100000000000000000000)
  directionLo := (7287531028049507897/2500000000000000000)
  directionHi := (291501241121980315881/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree035.table
  base := (-6694954614293410112250439738633664555077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-4011083140473775010529742407363198000000000000)
      constant := (33382856702173921302940369609280002702029608609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree035.table
  base := (-6696249187896938286688405576960203413811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-4021611549344971537161986413437573000000000000)
      constant := (33563761807144598950110551590974534756906893687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7287531028049507897/2500000000000000000)
  centralHi := (291501241121980315881/100000000000000000000)
  directionLo := (36969619850464133481/12500000000000000000)
  directionHi := (295756958803713067849/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree036.table
  base := (-855988177399922979977457608918621535311/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-7487455019951790771983776054008481000000000000)
      constant := (64165146302460585210818818615606426223519303752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree036.table
  base := (-6848975074367945818334843736280050908421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-7507108049844690955030631532013981000000000000)
      constant := (64512575876103559827367477625014509330034622659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36969619850464133481/12500000000000000000)
  centralHi := (295756958803713067849/100000000000000000000)
  directionLo := (74988075629557409307/25000000000000000000)
  directionHi := (299952302518229637229/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree037.table
  base := (-3483145591946359396105790674095855660381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-207779497194181726171166528955661272000000000000)
      constant := (1832188068026020015277416058168165509680284380946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree037.table
  base := (-3483587158070411365112102737146259842609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-208324868773709706250716768470313897000000000000)
      constant := (1842099109614836255539032920570407141990331098394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/25000000000000000000)
  centralHi := (299952302518229637229/100000000000000000000)
  directionLo := (152044885552880296803/50000000000000000000)
  directionHi := (304089771105760593607/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree038.table
  base := (-705055375253314771157351261875523758071/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-213397708849665101498771104453093557000000000000)
      constant := (1934943866130082285268504742614618730815992852430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree038.table
  base := (-1410256470931806922973798393233799522869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-213957820201612756715606485576250307000000000000)
      constant := (1945399595798348648335887344487175270390237658885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152044885552880296803/50000000000000000000)
  centralHi := (304089771105760593607/100000000000000000000)
  directionLo := (308171695644360225553/100000000000000000000)
  directionHi := (154085847822180112777/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree039.table
  base := (-7101048167683343370609054837007710927007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-24335102278349830758486186661169538000000000000)
      constant := (226747062166774794859690149467977401066324998059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree039.table
  base := (-7101648863110640789159673763557437595457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-8132991541833918784462822321562471000000000000)
      constant := (75990306086867335290660077220631208672330236903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308171695644360225553/100000000000000000000)
  centralHi := (154085847822180112777/50000000000000000000)
  directionLo := (312200254806889150359/100000000000000000000)
  directionHi := (7805006370172228759/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree040.table
  base := (-7118059722245517162849767465544147824787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-224634132160631852153980255447958127000000000000)
      constant := (2149524910282053050064510946920619843004466511271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree040.table
  base := (-7118554639548304304303831745732965094403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-225223723057418857645385919788123127000000000000)
      constant := (2161112912657305910572740446655056237690841542999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312200254806889150359/100000000000000000000)
  centralHi := (7805006370172228759/2500000000000000000)
  directionLo := (63235497691297672859/20000000000000000000)
  directionHi := (39522186057061045537/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree041.table
  base := (-443863603843442574191637821198112361661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-230252343816115227481584830945390412000000000000)
      constant := (2261346120258022208295036699558515521910646155408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree041.table
  base := (-7102225172615367610508775614835577653381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-230856674485321908110275636894059537000000000000)
      constant := (2273521771985986104227272128387879896903176659473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63235497691297672859/20000000000000000000)
  centralHi := (39522186057061045537/12500000000000000000)
  directionLo := (320105309721377714103/100000000000000000000)
  directionHi := (40013163715172214263/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree042.table
  base := (-7052506193381251176367050014343324669197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-178284622427512171435517314015739000000000000)
      constant := (1796058763786383255949229011344306428036330987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree042.table
  base := (-3526420767666199506568469444990180712739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2525754)
      previous := (1262877)
      next := (1262877)
      square := (12970999729314120810924615483630000000000000)
      linear := (-536257655132029384524184476190467000000000000)
      constant := (5417150616740483908494507352264238311325022814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320105309721377714103/100000000000000000000)
  centralHi := (40013163715172214263/12500000000000000000)
  directionLo := (161992757875919776023/50000000000000000000)
  directionHi := (323985515751839552047/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree043.table
  base := (-6970273335913603067909261387613044286923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-241488767127081978136793981940254982000000000000)
      constant := (2494042621912957247749243816032227632164408764159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree043.table
  base := (-3485274566623763240543370444433594749007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-242122577341128009040055071105932357000000000000)
      constant := (2507436722076146121316544171214871742475881817062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161992757875919776023/50000000000000000000)
  centralHi := (323985515751839552047/100000000000000000000)
  directionLo := (163909898665510585539/50000000000000000000)
  directionHi := (327819797331021171079/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree044.table
  base := (-6855238026542812154484116284358433164463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-2042206436219548375738831053204027000000000000)
      constant := (21610874541945511590813047996917428853247357099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree044.table
  base := (-1713866182392054089272568136132165034897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-2047566353463066607478882547205527000000000000)
      constant := (21726783110482163275587073807091798549130928724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163909898665510585539/50000000000000000000)
  centralHi := (327819797331021171079/100000000000000000000)
  directionLo := (165804873742690474133/50000000000000000000)
  directionHi := (331609747485380948267/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree045.table
  base := (-6707495834960505824989902449302232660199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-9360192238446249214518634553152576000000000000)
      constant := (101437206956358137676321545612517670440326326321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree045.table
  base := (-670768208664215515383985224767426271331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-9384758525812374443327203900659451000000000000)
      constant := (101980547754851962164222152771710345522266465490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165804873742690474133/50000000000000000000)
  centralHi := (331609747485380948267/100000000000000000000)
  directionLo := (2682854953753371283/800000000000000000)
  directionHi := (41919608652396426297/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree046.table
  base := (-3263561776833456045386475528809482506949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-258343402093532104119607708432551837000000000000)
      constant := (2865708324286228806029875205822874574960328156834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree046.table
  base := (-6527276496308470042854512736996052136383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-259021431624837160434724222423741587000000000000)
      constant := (2881038230519899120825514969171592885306718610339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2682854953753371283/800000000000000000)
  centralHi := (41919608652396426297/12500000000000000000)
  directionLo := (67812516495894991313/20000000000000000000)
  directionHi := (169531291239737478283/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree047.table
  base := (-6314182886758924189398888329854228839409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-263961613749015479447212283929984122000000000000)
      constant := (2995626544958013963748647541510784858375343563597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree047.table
  base := (-6314308417963303584022026051607490983543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-264654383052740210899613939529677997000000000000)
      constant := (3011630605537476061739275267308815672023192810619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67812516495894991313/20000000000000000000)
  centralHi := (169531291239737478283/50000000000000000000)
  directionLo := (137091292177332447/40000000000000000)
  directionHi := (342728230443331117501/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree048.table
  base := (-6068723414084275430237469547995355346049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-29953313933833206086090762158601823000000000000)
      constant := (347617651214375302282241183377355048108531495413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree048.table
  base := (-6068826400080197385184401740453850762351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-10010642017801602272759394690207941000000000000)
      constant := (116490797541342762706521428553010414822671025129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137091292177332447/40000000000000000)
  centralHi := (342728230443331117501/100000000000000000000)
  directionLo := (346355085205895886277/100000000000000000000)
  directionHi := (173177542602947943139/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree049.table
  base := (-2895392486554318527828676195573354525293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (463914)
      previous := (231957)
      next := (231957)
      square := (2382428521710756883639215088830000000000000)
      linear := (-114618091236977188714044745907892000000000000)
      constant := (1359643881596239167421629130755579826531735538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree049.table
  base := (-2895434713156204866555983449324683776173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (463914)
      previous := (231957)
      next := (231957)
      square := (2382428521710756883639215088830000000000000)
      linear := (-114918902919011375189251717510017000000000000)
      constant := (1366889091614263495237898051100790516206485618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346355085205895886277/100000000000000000000)
  centralHi := (173177542602947943139/50000000000000000000)
  directionLo := (174972176468967288383/50000000000000000000)
  directionHi := (349944352937934576767/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree050.table
  base := (-2740199786439912146581594655001645353377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-280816248715465605430026010422280977000000000000)
      constant := (3403464590226475856217963482519674267475744271482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree050.table
  base := (-5480468799508564471837987350518857741461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-281553237336449362294283090847487227000000000000)
      constant := (3421577886044610342419224729239152070112511238113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174972176468967288383/50000000000000000000)
  centralHi := (349944352937934576767/100000000000000000000)
  directionLo := (8837429464298288003/2500000000000000000)
  directionHi := (353497178571931520121/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree051.table
  base := (-5137592932003783221722850907674641696009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-10608683717442554842875206885915306000000000000)
      constant := (131312501878986162170898340787579818294833769311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree051.table
  base := (-5137649654651934058657898417877833077043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-31909576529372490306574756439269293000000000000)
      constant := (396031429743561425677877007012361765169873171791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/2500000000000000000)
  centralHi := (353497178571931520121/100000000000000000000)
  directionLo := (357014650068428371059/100000000000000000000)
  directionHi := (17850732503421418553/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree052.table
  base := (-4762385714491462764463132155622747899557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-292052672026432356085235161417145547000000000000)
      constant := (3690423679141135436081622269927678737751765621681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree052.table
  base := (-74413002715763241492698170536933452537/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-292819140192255463224062525059360047000000000000)
      constant := (3710015495598693635289535821733288827520540929344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357014650068428371059/100000000000000000000)
  centralHi := (17850732503421418553/5000000000000000000)
  directionLo := (360497802307654412021/100000000000000000000)
  directionHi := (180248901153827206011/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree053.table
  base := (-1088698630706733250134174145450803246373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-297670883681915731412839736914577832000000000000)
      constant := (3838422845221005616486495892567005070651530724036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree053.table
  base := (-435483256177727350772912745835612943413/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-298452091620158513688952242165296457000000000000)
      constant := (3858775642653011765898967697995978286858012193290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360497802307654412021/100000000000000000000)
  centralHi := (180248901153827206011/50000000000000000000)
  directionLo := (72789524129180842869/20000000000000000000)
  directionHi := (181973810322952107173/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree054.table
  base := (-3914832695948439154989912769570378542137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-11232929456940707657053493052296671000000000000)
      constant := (147756849790396726497080825033633613055559816623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree054.table
  base := (-3914863829567224161803546714574481605819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-11262409001780057931623776269304921000000000000)
      constant := (148539378029473072279614834829488226029395858301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72789524129180842869/20000000000000000000)
  centralHi := (181973810322952107173/50000000000000000000)
  directionLo := (367365044171300169113/100000000000000000000)
  directionHi := (183682522085650084557/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree055.table
  base := (-3442510950465609358511179839363767844199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-2552952950354400678248337916606962000000000000)
      constant := (34243470185441731380028734389483615646964111427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree055.table
  base := (-1721268211780936433171076063730739791257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-2559652846908798467923402284108837000000000000)
      constant := (34424612446982212165604157447004339663104364922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367365044171300169113/100000000000000000000)
  centralHi := (183682522085650084557/50000000000000000000)
  directionLo := (370750968689425874543/100000000000000000000)
  directionHi := (23171935543089117159/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree056.table
  base := (-2937837895907879195437322338514722569421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-6418888135680935865217417620548463000000000000)
      constant := (87765257591438643468931784610382105666919378057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree056.table
  base := (-2937858730753795227573929071347870158613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-6435733589874850307829008030267463000000000000)
      constant := (88228985198614372159319376560239526901398755121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370750968689425874543/100000000000000000000)
  centralHi := (23171935543089117159/6250000000000000000)
  directionLo := (187053124732864303733/50000000000000000000)
  directionHi := (374106249465728607467/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree057.table
  base := (-2400820448749849877130924310067675457563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-35571525589316581413695337656034108000000000000)
      constant := (495616453190394837633723862191661465700180019031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree057.table
  base := (-2400837484464430430728141364470881457663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-11888292493769285761055967058853411000000000000)
      constant := (166077394811885857087032443916218097048038287577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187053124732864303733/50000000000000000000)
  centralHi := (374106249465728607467/100000000000000000000)
  directionLo := (188715851874239943789/50000000000000000000)
  directionHi := (377431703748479887579/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree058.table
  base := (-1831464165098266967246573632875611771041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-325761941959332608050862614401739257000000000000)
      constant := (4623611219055155951807789450397096834601965736253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree058.table
  base := (-36629561802951438960231699967919147287/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-326616848759673766013400827694978507000000000000)
      constant := (4647986219250547667267629908332809728904895188550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188715851874239943789/50000000000000000000)
  centralHi := (377431703748479887579/100000000000000000000)
  directionLo := (380728113093381387143/100000000000000000000)
  directionHi := (47591014136672673393/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree059.table
  base := (-307443377004791056990166546709311775389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-331380153614815983378467189899171542000000000000)
      constant := (4789687007996711775035707802824704629264838931748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree059.table
  base := (-61489244350860738709591612580579746047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-332249800187576816478290544800914917000000000000)
      constant := (4814909918683907509483289732856693714463286937020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380728113093381387143/100000000000000000000)
  centralHi := (47591014136672673393/12500000000000000000)
  directionLo := (76799245101709933009/20000000000000000000)
  directionHi := (191998112754274832523/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree060.table
  base := (-2978760311724438500913805012582305747/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-12481420935937013285410065385059401000000000000)
      constant := (183658348793279848232414462778947350190415162600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree060.table
  base := (-595761358139938261368174596640068498317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-37542527957275540771464473545205703000000000000)
      constant := (553873414544398894899796891816283021979401340529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76799245101709933009/20000000000000000000)
  centralHi := (191998112754274832523/50000000000000000000)
  directionLo := (96809189359139368223/25000000000000000000)
  directionHi := (387236757436557472893/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree061.table
  base := (17649323180382397040224511630153739801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-342616576925782734033676340894036112000000000000)
      constant := (5130876424736026835851971199015126050746198442668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree061.table
  base := (70589700857560361334666332696690750813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-343515703043382917408069979012787737000000000000)
      constant := (5157838633968512181058308120950321484927657476471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96809189359139368223/25000000000000000000)
  centralHi := (387236757436557472893/100000000000000000000)
  directionLo := (390450395588409629807/100000000000000000000)
  directionHi := (24403149724275601863/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree062.table
  base := (96159030614243950026119497519238454979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-348234788581266109361280916391468397000000000000)
      constant := (5305990011811554082861794976600501890838654076744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree062.table
  base := (769266046314402182527313750386317540829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-349148654471285967872959696118724147000000000000)
      constant := (5333843610291247630903872682070290919673537911543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390450395588409629807/100000000000000000000)
  centralHi := (24403149724275601863/6250000000000000000)
  directionLo := (39363779864275215577/10000000000000000000)
  directionHi := (393637798642752155771/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree063.table
  base := (375067734365158360100713658039288039779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-267462585212962573460986766355934000000000000)
      constant := (4145212520091077605923652679598208630151398764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree063.table
  base := (1500265877749031089259007711658676523871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-268164479137709008569803033427559000000000000)
      constant := (4166950601469915680438866501132851293110031159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39363779864275215577/10000000000000000000)
  centralHi := (393637798642752155771/100000000000000000000)
  directionLo := (198399799411112190109/50000000000000000000)
  directionHi := (396799598822224380219/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree064.table
  base := (565897969884572667706452804844946652993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-359471211892232860016490067386332967000000000000)
      constant := (5665254869848733876886487169963430952630011370124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree064.table
  base := (2263587750503657346361071096620790683083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-360414557327092068802739130330596967000000000000)
      constant := (5694934728996872129253975858105927963711078818561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198399799411112190109/50000000000000000000)
  centralHi := (396799598822224380219/100000000000000000000)
  directionLo := (24996025209852469769/6250000000000000000)
  directionHi := (79987280671527903261/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree065.table
  base := (3059233874321039479994987110186938815679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-365089423547716235344094642883765252000000000000)
      constant := (5849406119728286275658792245588772438720086726493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree065.table
  base := (3059230505598354940563236749453614398017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-366047508754995119267628847436533377000000000000)
      constant := (5880020850956652491700804248713643994730210015139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/6250000000000000000)
  centralHi := (79987280671527903261/20000000000000000000)
  directionLo := (201524397924798954969/50000000000000000000)
  directionHi := (403048795849597909939/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree066.table
  base := (194359798058377596492710450487647392737/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (1022826)
      previous := (511413)
      next := (511413)
      square := (5252718898647867105250464121470000000000000)
      linear := (-340411051609916997861982753334433000000000000)
      constant := (5543223054346940247602225205598008483397692220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree066.table
  base := (1943596606702477359188483262091835185723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (340942)
      previous := (170471)
      next := (170471)
      square := (1750906299549289035083488040490000000000000)
      linear := (-113768123716834456606219334111561000000000000)
      constant := (1857402511273943645128193503481125992561841846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201524397924798954969/50000000000000000000)
  centralHi := (403048795849597909939/100000000000000000000)
  directionLo := (10153433438404505239/2500000000000000000)
  directionHi := (406137337536180209561/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree067.table
  base := (94949547383376348028039486000172920517/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-376325846858682985999303793878629822000000000000)
      constant := (6226746223168266908627420920248997389631051131950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree067.table
  base := (4747475128418548197337484249453097540247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-377313411610801220197408281648406197000000000000)
      constant := (6259274183275045869087665610155377289463232664549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10153433438404505239/2500000000000000000)
  centralHi := (406137337536180209561/100000000000000000000)
  directionLo := (25575160529657443921/6250000000000000000)
  directionHi := (409202568474519102737/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree068.table
  base := (705009684978069454036679140794796317243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-381944058514166361326908369376062107000000000000)
      constant := (6419935065830075574727974680282682255510458778248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree068.table
  base := (5640075652940587276474897143428902477733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-382946363038704270662297998754342607000000000000)
      constant := (6453441383097480975955645947597745626771803660111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25575160529657443921/6250000000000000000)
  centralHi := (409202568474519102737/100000000000000000000)
  directionLo := (103061252160823582199/25000000000000000000)
  directionHi := (412245008643294328797/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree069.table
  base := (1312999159410958362144090296195683742587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-14354158154431471727944923884203496000000000000)
      constant := (245042090010294791413272190173886599557900589135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree069.table
  base := (5251995446334506261238511950789009399/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-43175479385178591236354190651142113000000000000)
      constant := (738959511115728428684562290343257953748525796250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103061252160823582199/25000000000000000000)
  centralHi := (412245008643294328797/100000000000000000000)
  directionLo := (83053031794504922017/20000000000000000000)
  directionHi := (207632579486262305043/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree070.table
  base := (7522231923105436164013496538889509446099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-8024091465819043101675867762671973000000000000)
      constant := (139088781905957317535055299982610784340659866217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree070.table
  base := (1504446141905913834464640837579930281411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-8045148283561436154940355774820723000000000000)
      constant := (139813404716256082577533138850927024896195585565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83053031794504922017/20000000000000000000)
  centralHi := (207632579486262305043/50000000000000000000)
  directionLo := (209131751153215886743/50000000000000000000)
  directionHi := (418263502306431773487/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree071.table
  base := (2127946384797457316165303817810846254117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-398798693480616487309722095868358962000000000000)
      constant := (7017576712671339232650475677222714323000971095356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree071.table
  base := (4255892275192382134523074399757293120683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-399845217322413422056967150072151837000000000000)
      constant := (7054105073851268749471938606975140578954553075522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209131751153215886743/50000000000000000000)
  centralHi := (418263502306431773487/100000000000000000000)
  directionLo := (421240504304617860569/100000000000000000000)
  directionHi := (42124050430461786057/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree072.table
  base := (953365638993571607743336515253211927547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-14978403893929624542123210050584861000000000000)
      constant := (267511689856040530000711618004554165824028819870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree072.table
  base := (595853474026914362845228195477355576451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-15017709953715424908216921006595861000000000000)
      constant := (268902975050950409533688435190482761110817935536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421240504304617860569/100000000000000000000)
  centralHi := (42124050430461786057/10000000000000000000)
  directionLo := (26512288392894864009/6250000000000000000)
  directionHi := (84839322857263564829/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree073.table
  base := (10587844270889921990070837449998133973543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-410035116791583237964931246863223532000000000000)
      constant := (7431067052113429391302664255588637356888447519381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree073.table
  base := (5293921807416046355904005938460255590823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-411111120178219522986746584284024657000000000000)
      constant := (7469682587125737469001505793430540109383080394282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512288392894864009/6250000000000000000)
  centralHi := (84839322857263564829/20000000000000000000)
  directionLo := (427132266022061859361/100000000000000000000)
  directionHi := (213566133011030929681/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree074.table
  base := (11674349018479901945234146269461466166751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-415653328447066613292535822360655817000000000000)
      constant := (7642330989389270473710537616520236422530228016317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree074.table
  base := (116743484842422793667633487188132424151/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-416744071606122573451636301389961067000000000000)
      constant := (7682011854867258565322970259748396536991286211700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427132266022061859361/100000000000000000000)
  centralHi := (213566133011030929681/50000000000000000000)
  directionLo := (215023939238348377897/50000000000000000000)
  directionHi := (86009575695339351159/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree075.table
  base := (12793170501949373984031146698233393769441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-46807948900283332068904488650898678000000000000)
      constant := (872956381879439613431821393160991131998875306283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree075.table
  base := (6396585033495591172538926263565964595887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-15643593445704652737649111796144351000000000000)
      constant := (292495115874609644008864363793318720200723374254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215023939238348377897/50000000000000000000)
  centralHi := (86009575695339351159/20000000000000000000)
  directionLo := (216471928253684928923/50000000000000000000)
  directionHi := (432943856507369857847/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree076.table
  base := (6972154308440049937581359297208737664527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-426889751758033363947744973355520387000000000000)
      constant := (8073896393871423876121957225940603459451946622618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree076.table
  base := (13944308262814804896763608644816922919357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-428009974461928674381415735601833887000000000000)
      constant := (8115751407580865429555921029683908928113271904919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216471928253684928923/50000000000000000000)
  centralHi := (432943856507369857847/100000000000000000000)
  directionLo := (27238786969985493351/6250000000000000000)
  directionHi := (435820591519767893617/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree077.table
  base := (15127763279988093308766780072187459423301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (187866)
      previous := (93933)
      next := (93933)
      square := (964785103833281713209268920270000000000000)
      linear := (-72947877114777658842190849865568000000000000)
      constant := (1398920198955201108243479633652113133817027223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree077.table
  base := (15127762991821239969214124733653634620081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (187866)
      previous := (93933)
      next := (93933)
      square := (964785103833281713209268920270000000000000)
      linear := (-73139302730617595690049831794193000000000000)
      constant := (1406166586463112871916731663181879758602367163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27238786969985493351/6250000000000000000)
  centralHi := (435820591519767893617/100000000000000000000)
  directionLo := (109669615521405558327/25000000000000000000)
  directionHi := (438678462085622233309/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree078.table
  base := (817176721247189040822937786588442833789/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-16226895372925930170479782383347591000000000000)
      constant := (315463401244316792091846744933143083010304281380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree078.table
  base := (16343534190449935666713828178260386944383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-48808430813081641701243907757078523000000000000)
      constant := (951288775421408836080834540205061646626407280629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109669615521405558327/25000000000000000000)
  centralHi := (438678462085622233309/100000000000000000000)
  directionLo := (441517834524238696771/100000000000000000000)
  directionHi := (110379458631059674193/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree079.table
  base := (8795810999507426759868232587055224791769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-443744386724483489930558699847817242000000000000)
      constant := (8743838315431286159327105359058812385558394169046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree079.table
  base := (1759162180822841631081103706596054736093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-444908828745637825776084886919643117000000000000)
      constant := (8789063270143605870077902073018754465855808102310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441517834524238696771/100000000000000000000)
  centralHi := (110379458631059674193/25000000000000000000)
  directionLo := (222169531725290442047/50000000000000000000)
  directionHi := (88867812690116176819/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree080.table
  base := (18872025960370092583160703408687399679071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-449362598379966865258163275345249527000000000000)
      constant := (8973177304781458806080473387142815005138411421757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree080.table
  base := (9436012902584643741908698120586683830853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-450541780173540876240974604025579527000000000000)
      constant := (9019554564878911452677702221564793214554055198302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222169531725290442047/50000000000000000000)
  centralHi := (88867812690116176819/20000000000000000000)
  directionLo := (447142492292228547167/100000000000000000000)
  directionHi := (13973202884132142099/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree081.table
  base := (2523093284489278391167102079906511283989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-16851141112424082984658068549728956000000000000)
      constant := (340945511162498881651649398060270386892886146152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree081.table
  base := (20184746149681317480855421083563930987361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-16895360429683108396513493375241331000000000000)
      constant := (342706402324103427200789929308529422794379105081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447142492292228547167/100000000000000000000)
  centralHi := (13973202884132142099/3125000000000000000)
  directionLo := (224964226888672227921/50000000000000000000)
  directionHi := (449928453777344455843/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree082.table
  base := (21529782919549416536844370905531868194703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-460599021690933615913372426340114097000000000000)
      constant := (9440892805044605944479542921358814678754419377101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree082.table
  base := (215297828168932524314460491211378038741/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-461807683029346977170754038237452347000000000000)
      constant := (9489618163564157333574732594187748108821299964700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224964226888672227921/50000000000000000000)
  centralHi := (449928453777344455843/100000000000000000000)
  directionLo := (452697270395612510761/100000000000000000000)
  directionHi := (226348635197806255381/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree083.table
  base := (22907135870779465861826354992339834312339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-466217233346416991240977001837546382000000000000)
      constant := (9679269315592093699350825273945680248739886042713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree083.table
  base := (22907135787308989305523644709381929251669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-467440634457250027635643755343388757000000000000)
      constant := (9729190467166077111731177869744005692639351497823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452697270395612510761/100000000000000000000)
  centralHi := (226348635197806255381/50000000000000000000)
  directionLo := (22772462741697736071/5000000000000000000)
  directionHi := (455449254833954721421/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree084.table
  base := (24316805113589369059172712635675856816261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2525754)
      previous := (1262877)
      next := (1262877)
      square := (12970999729314120810924615483630000000000000)
      linear := (-1069921643995238926459368656088387000000000000)
      constant := (22495823884136758024456082770247869465190834407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree084.table
  base := (189975039419755975045811020673970326553/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-357576406564741555631544574791629000000000000)
      constant := (7537256064578476120334916728882650168464990336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22772462741697736071/5000000000000000000)
  centralHi := (455449254833954721421/100000000000000000000)
  directionLo := (229092355194346756381/50000000000000000000)
  directionHi := (458184710388693512763/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree085.table
  base := (25758790635546021603207350661728873682051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-477453656657383741896186152832410952000000000000)
      constant := (10165059856883729607865058109406088619121544741417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree085.table
  base := (3219848822547986684349524256335166227163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-478706537313056128565423189555261577000000000000)
      constant := (10217416082285583362758591569977858166736030335368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229092355194346756381/50000000000000000000)
  centralHi := (458184710388693512763/100000000000000000000)
  directionLo := (230451965677848618031/50000000000000000000)
  directionHi := (460903931355697236063/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree086.table
  base := (27233092427076588334736710429384786201949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-483071868312867117223790728329843237000000000000)
      constant := (10412473887455261696221932157176686858748763486583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree086.table
  base := (340413654778036591592851220509808977591/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-484339488740959179030312906661197987000000000000)
      constant := (10466069393640012195297154777452897539194024207760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230451965677848618031/50000000000000000000)
  centralHi := (460903931355697236063/100000000000000000000)
  directionLo := (463607203399929486731/100000000000000000000)
  directionHi := (115901800849982371683/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree087.table
  base := (449057976263899456322748868633188466297/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-18099632591420388613014640882491686000000000000)
      constant := (394922237946730055835696474038304901845692527168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree087.table
  base := (14369855222227705776454569889685552405143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-54441382240984692166133624863014933000000000000)
      constant := (1190861078605208330922444637133226759221767297018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463607203399929486731/100000000000000000000)
  centralHi := (115901800849982371683/25000000000000000000)
  directionLo := (233147401952857878861/50000000000000000000)
  directionHi := (466294803905715757723/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree088.table
  base := (15139322395755222955962109505927113648269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-4085192492758957585776858506815767000000000000)
      constant := (90217681555042451633664379853732599992952668926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree088.table
  base := (15139322380953038743264643515065147686887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-4095912327245994049256961494818767000000000000)
      constant := (90681463005504522327637573573302732658195647098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233147401952857878861/50000000000000000000)
  centralHi := (466294803905715757723/100000000000000000000)
  directionLo := (58620875288617886087/12500000000000000000)
  directionHi := (468967002308943088697/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree089.table
  base := (995309229840919574989166037869947848693/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-499926503279317243206604454822140092000000000000)
      constant := (11172791018218927063531584234010622898897920141792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree089.table
  base := (15924947665428833658336262449223601423113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-501238343024668330424982057979007217000000000000)
      constant := (11230191342268213564652999385995935113088387441142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58620875288617886087/12500000000000000000)
  centralHi := (468967002308943088697/100000000000000000000)
  directionLo := (235812030206159410599/50000000000000000000)
  directionHi := (471624060412318821199/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree090.table
  base := (33453462168203017073094477157705920338917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-18723878330918541427192927048873051000000000000)
      constant := (423416854619091276650495396447085721682782505757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree090.table
  base := (33453462148664883564266179425763983317211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-18773010905650791884810065743886801000000000000)
      constant := (425590839378986080617325316025106343197299456931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235812030206159410599/50000000000000000000)
  centralHi := (471624060412318821199/100000000000000000000)
  directionLo := (237133116342366273221/50000000000000000000)
  directionHi := (474266232684732546443/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree091.table
  base := (8772336307353749403986588237927222703501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-10431896461026203956363542975857238000000000000)
      constant := (238667992604780556351039496509036817993178202332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree091.table
  base := (35089345213545408013317804709455562198641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-10459270324091314925607377391650613000000000000)
      constant := (239892673194802008452794563780844337763445047203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237133116342366273221/50000000000000000000)
  centralHi := (474266232684732546443/100000000000000000000)
  directionLo := (476893766545690125933/100000000000000000000)
  directionHi := (238446883272845062967/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree092.table
  base := (36757544537285013705925691711280901903523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-516781138245767369189418181314436947000000000000)
      constant := (11960220706965389134696533711412566179351661948041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree092.table
  base := (36757544524396706313436011686099956838077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-518137197308377481819651209296816447000000000000)
      constant := (12021556312197587923896178131709889684134984139159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476893766545690125933/100000000000000000000)
  centralHi := (238446883272845062967/50000000000000000000)
  directionLo := (479506902635719640971/100000000000000000000)
  directionHi := (119876725658929910243/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree093.table
  base := (19229030045557708206985262126773246209013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-58044372211250082724113639645763248000000000000)
      constant := (1358746920300379742789792279784243378696331994638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree093.table
  base := (9614515020162389972942122770574149204877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-19398894397640019714242256533435291000000000000)
      constant := (455236986673519545080459968776968417604600283668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479506902635719640971/100000000000000000000)
  centralHi := (119876725658929910243/25000000000000000000)
  directionLo := (482105875073585715363/100000000000000000000)
  directionHi := (120526468768396428841/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree094.table
  base := (40190891890648794219369256662148776683383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-528017561556734119844627332309301517000000000000)
      constant := (12500236364846313759220692118522980961272494038661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree094.table
  base := (40190891882151053686664315248802944036241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-529403100164183582749430643508689267000000000000)
      constant := (12564267970506418318026757693973334355817524832147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482105875073585715363/100000000000000000000)
  centralHi := (120526468768396428841/25000000000000000000)
  directionLo := (484690911701090344689/100000000000000000000)
  directionHi := (48469091170109034469/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree095.table
  base := (10489009983992533315467951620068057350491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-533635773212217495172231907806733802000000000000)
      constant := (12774762953394743994008488229260152251293375547588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree095.table
  base := (41956039929071182941494297779370064186787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-535036051592086633214320360614625677000000000000)
      constant := (12840164303163093180537875710369345066275457742729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484690911701090344689/100000000000000000000)
  centralHi := (48469091170109034469/10000000000000000000)
  directionLo := (60907779289523086907/12500000000000000000)
  directionHi := (487262234316184695257/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree096.table
  base := (43753504227428735097188456448261107314799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-19972369809914847055549499381635781000000000000)
      constant := (483418594383386975343619057061996601158202720279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree096.table
  base := (43753504221828394250053524457184752721509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-60074333668887742631023341968951343000000000000)
      constant := (1457676404239814958647047071480027122636216548567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60907779289523086907/12500000000000000000)
  centralHi := (487262234316184695257/100000000000000000000)
  directionLo := (489820058895066892151/100000000000000000000)
  directionHi := (61227507361883361519/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree097.table
  base := (22791642382787990104740727136087168790861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-544872196523184245827441058801598372000000000000)
      constant := (13332853649720751845488632162641171431796645343374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree097.table
  base := (22791642380515150467466770598354966513341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-546301954447892734144099794826498497000000000000)
      constant := (13401037975496908819495902192612654908226806395694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489820058895066892151/100000000000000000000)
  centralHi := (61227507361883361519/12500000000000000000)
  directionLo := (123091148950973806319/25000000000000000000)
  directionHi := (492364595803895225277/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree098.table
  base := (47445381551115795974567645752054469213747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (463914)
      previous := (231957)
      next := (231957)
      square := (2382428521710756883639215088830000000000000)
      linear := (-229275471961127705603934041773857000000000000)
      constant := (5671144422119190412803116457037127950921311449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree098.table
  base := (5930672693428319425429003836266168675871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (463914)
      previous := (231957)
      next := (231957)
      square := (2382428521710756883639215088830000000000000)
      linear := (-229877095325196078554347984978107000000000000)
      constant := (5700131326607536892655087742702543584512564456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123091148950973806319/25000000000000000000)
  centralHi := (492364595803895225277/100000000000000000000)
  directionLo := (61862006250088016021/12500000000000000000)
  directionHi := (494896050000704128169/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree099.table
  base := (24669897292432653356137448201371028739237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (340942)
      previous := (170471)
      next := (170471)
      square := (1750906299549289035083488040490000000000000)
      linear := (-170219963218289255121717235934026000000000000)
      constant := (4255584441910049255936554973478489555005816074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree099.table
  base := (1973591783274858291433479344411054041763/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (340942)
      previous := (170471)
      next := (170471)
      square := (1750906299549289035083488040490000000000000)
      linear := (-170666622988582441100054860434151000000000000)
      constant := (4277324657859931922457413010193382518856824075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61862006250088016021/12500000000000000000)
  centralHi := (494896050000704128169/100000000000000000000)
  directionLo := (497414621228071422399/100000000000000000000)
  directionHi := (310884138267544639/62500000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree100.table
  base := (51266523867723640687800933824253359323649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-561726831489634371810254785293895227000000000000)
      constant := (14192583492363668881855764361207691650509777440483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree100.table
  base := (51266523865294354765544652656342395203941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-563200808731601885538768946144307727000000000000)
      constant := (14265051001635303223123298588552964172920191868047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497414621228071422399/100000000000000000000)
  centralHi := (310884138267544639/62500000000000000)
  directionLo := (24996025209852469769/5000000000000000000)
  directionHi := (499920504197049395381/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree101.table
  base := (53225569400647268342571152731058522478481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-567345043145117747137859360791327512000000000000)
      constant := (14485185119446292687499460773548292741367211022227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree101.table
  base := (2661278469933814036199424433893821694669/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-568833760159504936003658663250244137000000000000)
      constant := (14559109348413108264280823567487426497180743576460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24996025209852469769/5000000000000000000)
  centralHi := (499920504197049395381/100000000000000000000)
  directionLo := (12560347219070976059/2500000000000000000)
  directionHi := (502413888762839042361/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree102.table
  base := (2760846559231528343860483203659324904977/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-63662583866733458051718215143195533000000000000)
      constant := (1642311028108422477495642478164832154843129381020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree102.table
  base := (2760846559151578687346711232767830068097/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-21276544873607703202538828902080761000000000000)
      constant := (550229433243324787184013885070672142184272170740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12560347219070976059/2500000000000000000)
  centralHi := (502413888762839042361/100000000000000000000)
  directionLo := (504894960092656028667/100000000000000000000)
  directionHi := (126223740023164007167/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree103.table
  base := (7155076152586320502267917813849784911243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-578581466456084497793068511786192082000000000000)
      constant := (15079425892960175345366679026448186667860033162248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree103.table
  base := (28620304609696740804496852706259738383143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-580099663015311036933438097462116957000000000000)
      constant := (15156307049113391056957608786606121115559690725162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504894960092656028667/100000000000000000000)
  centralHi := (126223740023164007167/25000000000000000000)
  directionLo := (31710243676638025687/6250000000000000000)
  directionHi := (507363898826208410993/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree104.table
  base := (59296603509855020785478132502173942783091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-584199678111567873120673087283624367000000000000)
      constant := (15381065039407473657518850317871412190844732271097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree104.table
  base := (11859320701760588712841769764365196054103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-585732614443214087398327814568053367000000000000)
      constant := (15459446403052138870500160061181427239582597784505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31710243676638025687/6250000000000000000)
  centralHi := (507363898826208410993/100000000000000000000)
  directionLo := (101964176245835942207/20000000000000000000)
  directionHi := (127455220307294927759/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree105.table
  base := (7673114256644147414362928645391663962893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-445818510783863377511925671036324000000000000)
      constant := (11856172858900809280566036949532221780087940776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree105.table
  base := (61384914052299907253213219611174246771557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2525754)
      previous := (1262877)
      next := (1262877)
      square := (12970999729314120810924615483630000000000000)
      linear := (-1340965001975322308079858348467097000000000000)
      constant := (35749688796812177128266780781878766327325684359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101964176245835942207/20000000000000000000)
  centralHi := (127455220307294927759/25000000000000000000)
  directionLo := (512266079340086392029/100000000000000000000)
  directionHi := (51226607934008639203/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree106.table
  base := (31752770425804317641374355772880447378519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-595436101422534623775882238278488937000000000000)
      constant := (15993380851723095560442767473286985716454154793546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree106.table
  base := (31752770425458332012600870247774927630281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-596998517299020188328107248779926187000000000000)
      constant := (16074806118147582148660684947323616033504150785654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512266079340086392029/100000000000000000000)
  centralHi := (51226607934008639203/10000000000000000000)
  directionLo := (102939932222171198993/20000000000000000000)
  directionHi := (257349830555427997483/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree107.table
  base := (820731048827923770983171929826421880443/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-601054313078017999103486813775921222000000000000)
      constant := (16304057517607390524009656783933519977661870534480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree107.table
  base := (4103655244104549323461622972570792214323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-602631468726923238792996965885862597000000000000)
      constant := (16387026479320372592712448153840920160955647546256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102939932222171198993/20000000000000000000)
  centralHi := (257349830555427997483/50000000000000000000)
  directionLo := (129280447635362751683/25000000000000000000)
  directionHi := (517121790541451006733/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree108.table
  base := (33921871609013158368578623373000994309473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-22469352767907458312262644047161241000000000000)
      constant := (615472099629128842845293259528286586735564810866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree108.table
  base := (16960935804392839000463874652103312417561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-22528311857586158861403210481177741000000000000)
      constant := (618602734922978134069520952648538843707448957124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129280447635362751683/25000000000000000000)
  centralHi := (517121790541451006733/100000000000000000000)
  directionLo := (64941578476105478677/12500000000000000000)
  directionHi := (519532627808843829417/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree109.table
  base := (17515329696991254483449594413604831524669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-612290736388984749758695964770785792000000000000)
      constant := (16934448368868040678842891403146730966137863155292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree109.table
  base := (70061318787596158693335386837676781895407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-613897371582729339722776400097735417000000000000)
      constant := (17020548208955410177685107612214103449531959500269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64941578476105478677/12500000000000000000)
  centralHi := (519532627808843829417/100000000000000000000)
  directionLo := (260966164695314941097/50000000000000000000)
  directionHi := (104386465878125976439/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree110.table
  base := (18077802654252189853037639872747930561157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-5106685521028662190795872233621637000000000000)
      constant := (142596384745947081171969375518238965377952499356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree110.table
  base := (18077802654177433021443986351123445488937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-5120085314137457770146000968625387000000000000)
      constant := (143321070887875408709748777611693063402845275596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260966164695314941097/50000000000000000000)
  centralHi := (104386465878125976439/20000000000000000000)
  directionLo := (524321048183548788529/100000000000000000000)
  directionHi := (52432104818354878853/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree111.table
  base := (9324177338261799339788316116596168064561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-69280795522216833379322790640627818000000000000)
      constant := (1952987694018721769744874013961380916839823830744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree111.table
  base := (1165522167278937482063159794701710282047/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-23154195349575386690835401270726231000000000000)
      constant := (654302886976308343143752656003317927662436895168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524321048183548788529/100000000000000000000)
  centralHi := (52432104818354878853/10000000000000000000)
  directionLo := (822967083776824507/156250000000000000)
  directionHi := (526698933617167684481/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree112.table
  base := (15381588611227176486814610299024847779849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-12839701456233364811051218189042503000000000000)
      constant := (365359764175549125487357626872227329535707837335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree112.table
  base := (76907943055939408787467260509384709814367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-12873392364621193696274399008480503000000000000)
      constant := (367214965749893904169122347848974288501213312461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (822967083776824507/156250000000000000)
  centralHi := (526698933617167684481/100000000000000000000)
  directionLo := (529066131762965840291/100000000000000000000)
  directionHi := (132266532940741460073/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree113.table
  base := (79254783668023700951128970987959468892177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-634763583010918251069114266760514932000000000000)
      constant := (18231380149566815457504648304294462391399652163859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree113.table
  base := (39627391833932231094240800089042157340123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-636429177294341541582335268521481057000000000000)
      constant := (18323915697593353404219343213620559942000933200482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529066131762965840291/100000000000000000000)
  centralHi := (132266532940741460073/25000000000000000000)
  directionLo := (531422785439045935551/100000000000000000000)
  directionHi := (8303481022485092743/1562500000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree114.table
  base := (81633940542624581606796159535644888908297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-23717844246903763940619216379923971000000000000)
      constant := (687523865224815538972488601993606942770527352737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree114.table
  base := (81633940542495531227709004453832888196111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-71340236524693843560802776180824163000000000000)
      constant := (2073036119545865903797929171922102340534867091493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531422785439045935551/100000000000000000000)
  centralHi := (8303481022485092743/1562500000000000000)
  directionLo := (533769034310684393827/100000000000000000000)
  directionHi := (133442258577671098457/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree115.table
  base := (84045413680781487825448750448723920253129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-646000006321885001724323417755379502000000000000)
      constant := (18897921079118131694717495700092748740593200835643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree115.table
  base := (84045413680676910779223059939257248313731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-647695080150147642512114702733353877000000000000)
      constant := (18993761456709743199733042821876130641008542983977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533769034310684393827/100000000000000000000)
  centralHi := (133442258577671098457/25000000000000000000)
  directionLo := (53610501498692109741/10000000000000000000)
  directionHi := (536105014986921097411/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree116.table
  base := (43244601541656891337861194468108341151219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-651618217977368377051927993252811787000000000000)
      constant := (19235710303717579023693262242698329069498037935346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree116.table
  base := (17297840616645808840602577617334756338647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-653328031578050692977004419839290287000000000000)
      constant := (19333224839990639213559843825295295712745108786745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53610501498692109741/10000000000000000000)
  centralHi := (536105014986921097411/100000000000000000000)
  directionLo := (67303857639172188009/12500000000000000000)
  directionHi := (538430861113377504073/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree117.table
  base := (22241327187754384770940770487630685782707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-24342089986401916754797502546305336000000000000)
      constant := (725056001291652073650150637480045054232111281388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree117.table
  base := (44482654375474440424612178018167427308569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-24405962333553842349699782849823211000000000000)
      constant := (728730193546730833324441340710283490298225548898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67303857639172188009/12500000000000000000)
  centralHi := (538430861113377504073/100000000000000000000)
  directionLo := (33796668966342601127/6250000000000000000)
  directionHi := (540746703461481618033/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree118.table
  base := (5717108167791622276004268411941001911733/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-662854641288335127707137144247676357000000000000)
      constant := (19920326272595277616935074279451375435684187809776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree118.table
  base := (1143421633557629138065051379145042264553/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-664593934433856793906783854051163107000000000000)
      constant := (20021232614029093662792958971234663320278836564080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33796668966342601127/6250000000000000000)
  centralHi := (540746703461481618033/100000000000000000000)
  directionLo := (543052670014268373753/100000000000000000000)
  directionHi := (271526335007134186877/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree119.table
  base := (94014468885009854727318772238219696937499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-13642303121302418429280443260104258000000000000)
      constant := (413615367691540477380615160725359771369845652417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree119.table
  base := (47007234442482395763543782946778577097883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-13678099711464486619830072880757133000000000000)
      constant := (415709734791808504265322441983266466915120808578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543052670014268373753/100000000000000000000)
  centralHi := (271526335007134186877/50000000000000000000)
  directionLo := (136337221512228681289/25000000000000000000)
  directionHi := (545348886048914725157/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree120.table
  base := (96587523352778224032689923788073179200151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-74899007177700208706927366138060103000000000000)
      constant := (2290776918638993506580071102707562534283221206013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree120.table
  base := (24146880838185430007514734318706616930359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-25031845825543070179131973639371701000000000000)
      constant := (767457348076889761249329314566927480228899308156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136337221512228681289/25000000000000000000)
  centralHi := (545348886048914725157/100000000000000000000)
  directionLo := (547635474216160049671/100000000000000000000)
  directionHi := (68454434277020006209/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree121.table
  base := (9919289408867881081059926651947789470759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-5617432035163514493305379097024572000000000000)
      constant := (173304496076009948185473442028402678605208936930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree121.table
  base := (387472242533786102907530810249086828109/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-5632171807583189630590520705528697000000000000)
      constant := (174181378461709659364703033221734975262290468608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547635474216160049671/100000000000000000000)
  centralHi := (68454434277020006209/12500000000000000000)
  directionLo := (274956277308377167459/50000000000000000000)
  directionHi := (549912554616754334919/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree122.table
  base := (101830581093398727811713146961163664246207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-685327487910268629017555446237405497000000000000)
      constant := (21325708289229659663767863675565186844312752203869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree122.table
  base := (2545764527334369470187951313718785452487/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-687125740145468995766342722474908747000000000000)
      constant := (21433572192176544568377808659950846328917333785160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274956277308377167459/50000000000000000000)
  centralHi := (549912554616754334919/100000000000000000000)
  directionLo := (552180244875068977881/100000000000000000000)
  directionHi := (276090122437534488941/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree123.table
  base := (104500584367605076336836792316753165540811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-25590581465398222383154074879068066000000000000)
      constant := (803132779994575635055432401884773701281081952531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree123.table
  base := (20900116873517136024654214295246816735403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-76973187952596894025692493286760573000000000000)
      constant := (2421580510334476183678886508068252905671790224445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552180244875068977881/100000000000000000000)
  centralHi := (276090122437534488941/50000000000000000000)
  directionLo := (277219330104998928551/50000000000000000000)
  directionHi := (554438660209997857103/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree124.table
  base := (107202903911945572605435500701504725140129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-696563911221235379672764597232270067000000000000)
      constant := (22046474337073931908051192513998893417815756264643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree124.table
  base := (21440580782385972943729611154540514223397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-698391643001275096696122156686781567000000000000)
      constant := (22157903996373174352877978730042231016913895177995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277219330104998928551/50000000000000000000)
  centralHi := (554438660209997857103/100000000000000000000)
  directionLo := (55668791350326960539/10000000000000000000)
  directionHi := (556687913503269605391/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree125.table
  base := (109937539727049171792727608934581377114741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-702182122876718755000369172729702352000000000000)
      constant := (22411376120895762514965826038533279017165295091647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree125.table
  base := (54968769863518225849130529157563867116803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-704024594429178147161011873792717977000000000000)
      constant := (22524610402270145520089366084009213060886599115602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55668791350326960539/10000000000000000000)
  centralHi := (556687913503269605391/100000000000000000000)
  directionLo := (279464057682642841979/50000000000000000000)
  directionHi := (558928115365285683959/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree126.table
  base := (112704491813526684866684727706307809920531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-534996473569313779537395123376519000000000000)
      constant := (17217906584522921549053423728529758005018828299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree126.table
  base := (112704491813516384916365298382756772702133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-536400261418806649755027657519769000000000000)
      constant := (17304870605219948177830806356493823905350946557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279464057682642841979/50000000000000000000)
  centralHi := (558928115365285683959/100000000000000000000)
  directionLo := (561159374198592911199/100000000000000000000)
  directionHi := (701449217748241139/125000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree127.table
  base := (115503760171971384587235050226052683980027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-713418546187685505655578323724566922000000000000)
      constant := (23150217208362773662624904839656898688294158449809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree127.table
  base := (2310075203439260896917587617065506716549/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-715290497284984248090791308004590797000000000000)
      constant := (23267104221685366626606416129145671952678018239150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561159374198592911199/100000000000000000000)
  centralHi := (701449217748241139/125000000000000000)
  directionLo := (281690898129546752453/50000000000000000000)
  directionHi := (563381796259093504907/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree128.table
  base := (59167672401479799001488442609812147552329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-719036757843168880983182899221999207000000000000)
      constant := (23524156512017128622630619168701290461628709364086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree128.table
  base := (118335344802952845836809203018043928202247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-720923448712887298555681025110527207000000000000)
      constant := (23642891635212792514879351751270792157761615018549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281690898129546752453/50000000000000000000)
  centralHi := (563381796259093504907/100000000000000000000)
  directionLo := (8837429464298288003/1562500000000000000)
  directionHi := (565595485715090432193/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree129.table
  base := (30299811426762820886876479895335194211003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-80517218833183584034531941635492388000000000000)
      constant := (2655678702476809160098351355432010946613497630756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree129.table
  base := (60599622853522908537500456994097297652527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-26909496301510753667428546008017171000000000000)
      constant := (889692816714543037427581345234681476022619593134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8837429464298288003/1562500000000000000)
  centralHi := (565595485715090432193/100000000000000000000)
  directionLo := (56780054470426090457/10000000000000000000)
  directionHi := (567800544704260904571/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree130.table
  base := (124095462884790591439535399313201127206857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-730273181154135631638392050216863777000000000000)
      constant := (24281072639189503468162185285644485136286109167419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree130.table
  base := (62047731442393083057473426419924890697521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-732189351568693399485460459322400027000000000000)
      constant := (24403547469929243914121793898042317590198062915814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56780054470426090457/10000000000000000000)
  centralHi := (567800544704260904571/100000000000000000000)
  directionLo := (284998536694323093319/50000000000000000000)
  directionHi := (569997073388646186639/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree131.table
  base := (31755999084176601640403782702111611685647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-735891392809619006965996625714296062000000000000)
      constant := (24664049462715940312915696241156061851785792025396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree131.table
  base := (63511998168351412149545071968571774068923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-737822302996596449950350176428336437000000000000)
      constant := (24788415891126687198499168292590145347210989259682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284998536694323093319/50000000000000000000)
  centralHi := (569997073388646186639/100000000000000000000)
  directionLo := (286092585003870743279/50000000000000000000)
  directionHi := (572185170007741486559/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree132.table
  base := (64992423031656436679051842184619191073161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (340942)
      previous := (170471)
      next := (170471)
      square := (1750906299549289035083488040490000000000000)
      linear := (-226969575899939510956106887423241000000000000)
      constant := (7667596814470347706952837913344718355533319122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree132.table
  base := (129984846063309973716008757569801192947333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (1022826)
      previous := (511413)
      next := (511413)
      square := (5252718898647867105250464121470000000000000)
      linear := (-682695366780991276781671160270223000000000000)
      constant := (23118743172533540075693135939996783992799639599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286092585003870743279/50000000000000000000)
  centralHi := (572185170007741486559/100000000000000000000)
  directionLo := (143591232732441386951/25000000000000000000)
  directionHi := (114872986185953109561/20000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree133.table
  base := (13297801206510990257548913939979014855003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-15247506451440525665738893402227768000000000000)
      constant := (519164094483050647727537417559507198475334452490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree133.table
  base := (66489006032553777805628193516652176212633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-15287514405151072466941420625310393000000000000)
      constant := (521780280433064884051835729766297624649293857078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143591232732441386951/25000000000000000000)
  centralHi := (114872986185953109561/20000000000000000000)
  directionLo := (288268225350592824077/50000000000000000000)
  directionHi := (115307290140237129631/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree134.table
  base := (27200698868516731976860893182672891207183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-752746027776069132948810352206592917000000000000)
      constant := (25831054973104321169111692776205059011564271666305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree134.table
  base := (34000873585645440090924983793215816390449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-754721157280305601345019327746145667000000000000)
      constant := (25961183170123963436736132822266722609905520464332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288268225350592824077/50000000000000000000)
  centralHi := (115307290140237129631/20000000000000000000)
  directionLo := (144674955523642504693/25000000000000000000)
  directionHi := (578699822094570018773/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree135.table
  base := (34765323224051759146361823115339920254131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-28087564423390833639867219544593526000000000000)
      constant := (971336363821587171890739169213447982763601569004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree135.table
  base := (34765323224051374822470684795413937990281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-28161263285489209326292927587114151000000000000)
      constant := (976228133392743964632236865746584945715497705604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144674955523642504693/25000000000000000000)
  centralHi := (578699822094570018773/100000000000000000000)
  directionLo := (580855136154836209339/100000000000000000000)
  directionHi := (29042756807741810467/5000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree136.table
  base := (4442231491451253210176701433818091737299/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-763982451087035883604019503201457487000000000000)
      constant := (26624121179908687974735424639177794478784632161056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree136.table
  base := (8884462982902428665601234058585905071841/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-765987060136111702274798761958018487000000000000)
      constant := (26758163035664159090990506260287791486226569877552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580855136154836209339/100000000000000000000)
  centralHi := (29042756807741810467/5000000000000000000)
  directionLo := (7287531028049507897/1250000000000000000)
  directionHi := (583002482243960631761/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree137.table
  base := (72636919416865271517982717143406186793697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-769600662742519258931624078698889772000000000000)
      constant := (27025173043285335839193244868718806046973548891398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree137.table
  base := (72636919416864768152985786705971590678541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-771620011564014752739688479063954897000000000000)
      constant := (27161193472307691346530069813622091308758102132494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7287531028049507897/1250000000000000000)
  centralHi := (583002482243960631761/100000000000000000000)
  directionLo := (292570974042105701387/50000000000000000000)
  directionHi := (23405677923368456111/4000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree138.table
  base := (148428586218514076170239887829367170138501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-86135430488666959362136517132924673000000000000)
      constant := (3047693045924023893415271444990018582907422347063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree138.table
  base := (148428586218513261548554298656794295348203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-28787146777478437155725118376662641000000000000)
      constant := (1021009293019929692645581367566558908478855283763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292570974042105701387/50000000000000000000)
  centralHi := (23405677923368456111/4000000000000000000)
  directionLo := (587273619799963663713/100000000000000000000)
  directionHi := (293636809899981831857/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree139.table
  base := (15161564988121485776376217792333327169377/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-780837086053486009586833229693754342000000000000)
      constant := (27836314290004652684589617221172177920120135362590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree139.table
  base := (151615649881214198626087366769720552736217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-782885914419820853669467913275827717000000000000)
      constant := (27976335353358717328478347591706763869939919474539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587273619799963663713/100000000000000000000)
  centralHi := (293636809899981831857/50000000000000000000)
  directionLo := (147349395489538443291/25000000000000000000)
  directionHi := (117879516391630754633/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree140.table
  base := (77417514911122933929564838767701990282637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-16050108116509579283968118473289523000000000000)
      constant := (576457217823548739058644166634276920420830757742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree140.table
  base := (77417514911122667278179052232441866500587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-16092221751994365390497094497587023000000000000)
      constant := (579356057097403627051238281598936452630026937442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147349395489538443291/25000000000000000000)
  centralHi := (117879516391630754633/20000000000000000000)
  directionLo := (591513917607426135697/100000000000000000000)
  directionHi := (295756958803713067849/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree141.table
  base := (158086726042009283261529148008877253677417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-29336055902387139268223791877356256000000000000)
      constant := (1061463169013595419644259805189710368990616864257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree141.table
  base := (79043363021004425896361900915044555757191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-88239090808402994955471927498633393000000000000)
      constant := (3200398360531493070959782278067515324298809319066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591513917607426135697/100000000000000000000)
  centralHi := (295756958803713067849/50000000000000000000)
  directionLo := (118724541663204787597/20000000000000000000)
  directionHi := (296811354158011968993/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree142.table
  base := (161370738540896835390981320153096591156097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-797691721019936135569646956186051197000000000000)
      constant := (29075619960047289801658616700157465147500032326499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree142.table
  base := (16137073854089648632853066427118588441979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-799784768703530005064137064593636947000000000000)
      constant := (29221750694393769871238560893885262375843088885930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118724541663204787597/20000000000000000000)
  centralHi := (296811354158011968993/50000000000000000000)
  directionLo := (119144806841694540831/20000000000000000000)
  directionHi := (148931008552118176039/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree143.table
  base := (164687067319290154197417481198819771638701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-6638925063433219098324392823830442000000000000)
      constant := (243758238540475389740172212459667215961022069727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree143.table
  base := (41171766829822467954125673814168929625691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (9205434)
      previous := (4602717)
      next := (4602717)
      square := (47274470087830803947254177093230000000000000)
      linear := (-6656344794474653351479560179335317000000000000)
      constant := (244983001211626181679782304032197677803378681828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119144806841694540831/20000000000000000000)
  centralHi := (148931008552118176039/25000000000000000000)
  directionLo := (119563594800220669421/20000000000000000000)
  directionHi := (298908987000551673553/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree144.table
  base := (5251116011798784334291211546237477520903/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-29960301641885292082402078043737621000000000000)
      constant := (1108032824941507047708944811697542146619208334816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree144.table
  base := (168035712377560870270903347860613528739969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-30038913761456892814589499955759621000000000000)
      constant := (1113598614867605514268073024674216686983064533849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119563594800220669421/20000000000000000000)
  centralHi := (298908987000551673553/50000000000000000000)
  directionLo := (74988075629557409307/12500000000000000000)
  directionHi := (599904605036459274457/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree145.table
  base := (171416673716072074679501395595776814404337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-814546355986386261552460682678348052000000000000)
      constant := (30342038190119636925689295531434370117359184518579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree145.table
  base := (171416673716071889907408138863305774830113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-816683622987239156458806215911446177000000000000)
      constant := (30494409058852355331516608732693405129254319989571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74988075629557409307/12500000000000000000)
  centralHi := (599904605036459274457/100000000000000000000)
  directionLo := (60198400331663009989/10000000000000000000)
  directionHi := (601984003316630099891/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree146.table
  base := (174829951335176340113574173648165140479491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-820164567641869636880065258175780337000000000000)
      constant := (30770202613497133050386090056019249710985539529897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree146.table
  base := (174829951335176190660176946793082817649389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-822316574415142206923695933017382587000000000000)
      constant := (30924682518890558316681535663252667505190589825063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60198400331663009989/10000000000000000000)
  centralHi := (601984003316630099891/100000000000000000000)
  directionLo := (151014060883888151587/25000000000000000000)
  directionHi := (604056243535552606349/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree147.table
  base := (89137772617609149389248014748095453167259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (51546)
      previous := (25773)
      next := (25773)
      square := (264714280190084098182135009870000000000000)
      linear := (-38214761409475358054869259737758000000000000)
      constant := (1443906684416487583347174811156353923999430034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree147.table
  base := (178275545235218177898386655819433950814351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17182)
      previous := (8591)
      next := (8591)
      square := (88238093396694699394045003290000000000000)
      linear := (-12771677323384473404423861201711000000000000)
      constant := (483717941313691199338604835518508508048536471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151014060883888151587/25000000000000000000)
  centralHi := (604056243535552606349/100000000000000000000)
  directionLo := (121224279822063560197/20000000000000000000)
  directionHi := (303060699555158900493/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree148.table
  base := (181753455416533782611198554767633539631469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-831400990952836387535274409170644907000000000000)
      constant := (31635568980298512628392358025354517707316398144423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree148.table
  base := (181753455416533684846106462799616710556531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-833582477270948307853475367229255407000000000000)
      constant := (31794310446811292818353633552194973317925036451577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121224279822063560197/20000000000000000000)
  centralHi := (303060699555158900493/50000000000000000000)
  directionLo := (152044885552880296803/25000000000000000000)
  directionHi := (608179542211521187213/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree149.table
  base := (37052736375890064651387888830741499764569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-837019202608319762862878984668077192000000000000)
      constant := (32072770923727599550085884238673277525293817310615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree149.table
  base := (92631840939725122095178224938728724266079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-839215428698851358318365084335191817000000000000)
      constant := (32233664914699027821512904858044211843935299006586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152044885552880296803/25000000000000000000)
  centralHi := (608179542211521187213/100000000000000000000)
  directionLo := (24409229751707670053/4000000000000000000)
  directionHi := (305115371896345875663/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree150.table
  base := (188806224624287413284323926045691215631281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-31208793120881597710758650376500351000000000000)
      constant := (1204184643475764706471993357121682282656415387401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree150.table
  base := (94403112312143674671429672922587906828239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-93872042236306045420361644604569803000000000000)
      constant := (3630671820578707835192129028863896292677880935114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24409229751707670053/4000000000000000000)
  centralHi := (305115371896345875663/50000000000000000000)
  directionLo := (153068768404708403797/25000000000000000000)
  directionHi := (612275073618833615189/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree151.table
  base := (192381083651356757509084970700056882720787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-848255625919286513518088135662941762000000000000)
      constant := (32956212330655100235824999308991725089497995520729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree151.table
  base := (12023817728209794112603818488873229390993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-850481331554657459248144518547064637000000000000)
      constant := (33121454858341765942813343519980864410589092616496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153068768404708403797/25000000000000000000)
  centralHi := (612275073618833615189/100000000000000000000)
  directionLo := (307156300147056418811/50000000000000000000)
  directionHi := (614312600294112837623/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree152.table
  base := (3919765179219250297039710383060791740539/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-853873837574769888845692711160374047000000000000)
      constant := (33402451794158344876282532439397465348291726605650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree152.table
  base := (195988258960962473039672766561962451926767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-856114282982560509713034235653001047000000000000)
      constant := (33569890334101599947049650731322374848397839441389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307156300147056418811/50000000000000000000)
  centralHi := (614312600294112837623/100000000000000000000)
  directionLo := (308171695644360225553/50000000000000000000)
  directionHi := (616343391288720451107/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree153.table
  base := (49906937638350382784443484555915560365739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-31833038860379750524936936542881716000000000000)
      constant := (1253766806087322573135348758554505000427059440076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree153.table
  base := (199627750553401497328433671670976361033347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-31916564237424576302886072324405091000000000000)
      constant := (1260050104166303741165953239365100961383769003787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308171695644360225553/50000000000000000000)
  centralHi := (616343391288720451107/100000000000000000000)
  directionLo := (123673502592988298639/20000000000000000000)
  directionHi := (154591878241235373299/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree154.table
  base := (25412444803620445403014611848799625678003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (187866)
      previous := (93933)
      next := (93933)
      square := (964785103833281713209268920270000000000000)
      linear := (-145911664848327987772120401780273000000000000)
      constant := (5785793260457997453726749575371167238175983752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree154.table
  base := (50824889607240883971782187545251144537899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (187866)
      previous := (93933)
      next := (93933)
      square := (964785103833281713209268920270000000000000)
      linear := (-146294516080007861467838365637523000000000000)
      constant := (5814781968883427561333719693328516056894561508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123673502592988298639/20000000000000000000)
  centralHi := (154591878241235373299/25000000000000000000)
  directionLo := (620385030602458529773/100000000000000000000)
  directionHi := (310192515301229264887/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree155.table
  base := (207003682587931494831944589931778949854863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-870728472541220014828506437652670902000000000000)
      constant := (34759245224853836120617163493193013337476185647821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree155.table
  base := (6468865080872858522787293938768150482129/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-873013137266269661107703386970810277000000000000)
      constant := (34933358777162741907204926736727875070132869716576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620385030602458529773/100000000000000000000)
  centralHi := (310192515301229264887/50000000000000000000)
  directionLo := (622396008422916966347/100000000000000000000)
  directionHi := (155599002105729241587/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree156.table
  base := (210740123030581544431735385965863410137827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-97371853799633710017345668127789243000000000000)
      constant := (3913059412794998200361920228832980524329954913601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree156.table
  base := (210740123030581526561760472949209008967703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-32542447729413804132318263113953581000000000000)
      constant := (1310885269016706199174001807897992696494306043263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622396008422916966347/100000000000000000000)
  centralHi := (155599002105729241587/25000000000000000000)
  directionLo := (312200254806889150359/50000000000000000000)
  directionHi := (624400509613778300719/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree157.table
  base := (214508879757183465523981464956913356557509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-881964895852186765483715588647535472000000000000)
      constant := (35678836712161025915597599140375361744156989949103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree157.table
  base := (2145088797571834510767803123730315597141/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-884279040122075762037482821182683097000000000000)
      constant := (35857472752376934388660146287313194131511901244700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312200254806889150359/50000000000000000000)
  centralHi := (624400509613778300719/100000000000000000000)
  directionLo := (626398596351486382353/100000000000000000000)
  directionHi := (313199298175743191177/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree158.table
  base := (10915497638400036981821899277616151062893/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-887583107507670140811320164144967757000000000000)
      constant := (36143151215874029224395088559854414145389078116620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree158.table
  base := (218309952768000727956893858494544881276307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-889911991549978812502372538288619507000000000000)
      constant := (36324070243942409708063127383600141144238397620569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626398596351486382353/100000000000000000000)
  centralHi := (313199298175743191177/50000000000000000000)
  directionLo := (628390329823970707627/100000000000000000000)
  directionHi := (157097582455992676907/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree159.table
  base := (55535835515822690586443880740527892074003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-33081530339376056153293508875644446000000000000)
      constant := (1355943638010963435474024368400367085807925702252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree159.table
  base := (111071671031645376452032492954047726668959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (123761946)
      previous := (61880973)
      next := (61880973)
      square := (635578986736391919735306158697870000000000000)
      linear := (-99504993664209095885251361710506213000000000000)
      constant := (4088188304238834707226523196222699494597555825834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628390329823970707627/100000000000000000000)
  centralHi := (157097582455992676907/25000000000000000000)
  directionLo := (630375770252509793119/100000000000000000000)
  directionHi := (3939848564078186207/625000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree160.table
  base := (5650226191082625565423236333175100435519/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-898819530818636891466529315139832327000000000000)
      constant := (37080817743428949212099021042359901741917608630920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree160.table
  base := (5650226191082625374614473272326601873249/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-901177894405784913432151972500492327000000000000)
      constant := (37266346235000215056672599269011950759043626547320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630375770252509793119/100000000000000000000)
  centralHi := (3939848564078186207/625000000000000000)
  directionLo := (63235497691297672859/10000000000000000000)
  directionHi := (632354976912976728591/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree161.table
  base := (229907069508289275739762889790781957237077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-18457913111716740138655793686474788000000000000)
      constant := (766411627903566659352152418914954874185382997391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree161.table
  base := (45981413901657853914055377519205400989097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (22731786)
      previous := (11365893)
      next := (11365893)
      square := (116738997563827087298321539352670000000000000)
      linear := (-18506343792524244161164116114416913000000000000)
      constant := (770245402744825418460553696589160389032688075255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63235497691297672859/10000000000000000000)
  centralHi := (632354976912976728591/100000000000000000000)
  directionLo := (15858200203912202869/2500000000000000000)
  directionHi := (634328008156488114761/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree162.table
  base := (46767481531696742025923696415352725246987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-33705776078874208967471795042025811000000000000)
      constant := (1408538307327235114825576739726511567457399551135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree162.table
  base := (116918703829241852571403682821548797781177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (41253982)
      previous := (20626991)
      next := (20626991)
      square := (211859662245463973245102052899290000000000000)
      linear := (-33794214713392259791182644693050561000000000000)
      constant := (1415582601357040287528332723612311053560370646434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15858200203912202869/2500000000000000000)
  centralHi := (634328008156488114761/100000000000000000000)
  directionLo := (79536865178684592027/12500000000000000000)
  directionHi := (636294921429476736217/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree163.table
  base := (237800062094123108245911607592550935930953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-915674165785087017449343041632129182000000000000)
      constant := (38509911335112536237546410380924487903980102705851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree163.table
  base := (118900031047061552107606520666961973354601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-918076748689494064826821123818301557000000000000)
      constant := (38702462741432983482528891609756320681891410004534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79536865178684592027/12500000000000000000)
  centralHi := (636294921429476736217/100000000000000000000)
  directionLo := (12765115465864150089/2000000000000000000)
  directionHi := (638255773293207504451/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree164.table
  base := (60448758203859250467773261724086876840321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-921292377440570392776947617129561467000000000000)
      constant := (38992300879108131182703157098659662186024904902028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree164.table
  base := (241795032815436998613315756930081369392943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-923709700117397115291710840924237967000000000000)
      constant := (39187222248876933125379234210303854034969994219181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12765115465864150089/2000000000000000000)
  centralHi := (638255773293207504451/100000000000000000000)
  directionLo := (320105309721377714103/50000000000000000000)
  directionHi := (640210619442755428207/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree165.table
  base := (245822319822649821981061026633271892567579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (1022826)
      previous := (511413)
      next := (511413)
      square := (5252718898647867105250464121470000000000000)
      linear := (-851157565744769300371489616737368000000000000)
      constant := (36251334187166109630277900092568255567164271537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree165.table
  base := (245822319822649819348088487960285763355233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (340942)
      previous := (170471)
      next := (170471)
      square := (1750906299549289035083488040490000000000000)
      linear := (-284463621532078410087725913079331000000000000)
      constant := (12144171643395683239578500488035386117815914433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320105309721377714103/50000000000000000000)
  centralHi := (640210619442755428207/100000000000000000000)
  directionLo := (64215951472546362601/10000000000000000000)
  directionHi := (642159514725463626011/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree166.table
  base := (249881923115981043427407403950068529970151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-932528800751537143432156768124426037000000000000)
      constant := (39966117487261544426995540271479484490677372444117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree166.table
  base := (249881923115981041299487239033748679079589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-934975602973203216221490275136110787000000000000)
      constant := (40165822271724997113163264119286542136861794448463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64215951472546362601/10000000000000000000)
  centralHi := (642159514725463626011/100000000000000000000)
  directionLo := (322051256579449343543/50000000000000000000)
  directionHi := (644102513158898687087/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree167.table
  base := (253973842695645324641716922341368628565337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-938147012407020518759761343621858322000000000000)
      constant := (40457544551422768096691343954827326063789617305579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree167.table
  base := (253973842695645322922033182603495275117489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-940608554401106266686379992242047197000000000000)
      constant := (40659662787132516829059523814568744801205016587763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322051256579449343543/50000000000000000000)
  centralHi := (644102513158898687087/100000000000000000000)
  directionLo := (32301983397416000513/5000000000000000000)
  directionHi := (646039667948320010261/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree168.table
  base := (51619615712370528512495583299784680006921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (841918)
      previous := (420959)
      next := (420959)
      square := (4323666576438040270308205161210000000000000)
      linear := (-713352399140214583588334028056909000000000000)
      constant := (30953880666900386598362813021081538838805173045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree168.table
  base := (258098078561852641172761198651721446828901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2525754)
      previous := (1262877)
      next := (1262877)
      square := (12970999729314120810924615483630000000000000)
      linear := (-2145672348818615231635532220743727000000000000)
      constant := (93325465544666447539027614286112285374745662087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell057.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32301983397416000513/5000000000000000000)
  centralHi := (646039667948320010261/100000000000000000000)
  directionLo := (161992757875919776023/25000000000000000000)
  directionHi := (647971031503679104093/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree169.table
  base := (32781828839351052871997992831379913622841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-949383435717987269414970494616722892000000000000)
      constant := (41449436199922485919454727624393237155419220274776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree169.table
  base := (52450926142961684370592211605627317837351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1113857514)
      previous := (556928757)
      next := (556928757)
      square := (5720210880627527277617755428280830000000000000)
      linear := (-951874457256912367616159426453920017000000000000)
      constant := (41656424825922768093867072025066628708732381732585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell057.Kernel169
