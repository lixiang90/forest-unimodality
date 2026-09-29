import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell179.Parameters
import ForestUnimodality.BinomialMassData.Q29_54.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_54.Batch050_099
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel000
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
  base := (90548750609826821725256707/2500000000000000000000000)
  polynomial :=
    { denominator := 6750000000000000000000000000000000000000
      center := (29)
      previous := (0)
      next := (25)
      square := (1137637945016781344798051407500000000000)
      linear := (-4380802908450703497811318230000000000000)
      constant := (244481626646532418658193108900000000000000) }

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
  base := (90548750609826821725256707/2500000000000000000000000)
  polynomial :=
    { denominator := 594000000000000000000000000000000000000000
      center := (2557)
      previous := (0)
      next := (2195)
      square := (100112139161476758342228523860000000000000)
      linear := (-385510655943661907807396004240000000000000)
      constant := (21514383144894852841920993583200000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel001
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
  base := (115729918731383020335120433566249735867903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-1008487859557704356266993886850000000000000)
      constant := (28604906724960204483937208911036185815900429) }

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
  base := (231207248096078672049579354607246946483281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-244158345491257659173219008663387500000000000)
      constant := (6915217388044766963018137744015505014322911243) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel002
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
  base := (37875270394851225411932847119519999686469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 607500000000000000000000000000000000000000
      center := (2610)
      previous := (0)
      next := (2250)
      square := (102387415051510321031824626675000000000000)
      linear := (-614215597797141041463975246150000000000000)
      constant := (9745286037933540855317141530018359923811967) }

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
  base := (151194785100652969455154392572203047414379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-297488916290402673981776995227975000000000000)
      constant := (4708338216407574107062430280369628390624985737) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel003
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
  base := (5077080431522209374759155538041535604941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (58)
      previous := (0)
      next := (50)
      square := (2275275890033562689596102815000000000000)
      linear := (-16093050351453997884321189975000000000000)
      constant := (157102978008941507049563059710871461333407) }

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
  base := (101258118191976094067234221276249208241647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-38979943009949743198926109088062500000000000)
      constant := (379386031405622258460377432599679210200460749) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel004
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
  base := (69513596345312406063809418422004074725649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-3336635735334875072499727406400000000000000)
      constant := (22169508307797459918677624124946990158332707) }

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
  base := (69275523849941530789699300173436481101101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-404150057888692703598892968357150000000000000)
      constant := (2677210550112153756889834732425421603815672703) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel005
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
  base := (48363988511738570321958311539043264361123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-3776522407408030525821640617300000000000000)
      constant := (18940168290716279521845950269862513239752889) }

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
  base := (12043040805340270806124034882328889598353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-457480628687837718407450954921737500000000000)
      constant := (2288525531991941860609777038792541535316493036) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel006
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
  base := (16968500018982186492666118114704609706593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (580)
      previous := (0)
      next := (500)
      square := (22752758900335626895961028150000000000000)
      linear := (-234244948860065887730197434900000000000000)
      constant := (976703345170481189352334643847024462078011) }

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
  base := (8446219640547331618932997036283153485413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-56756799942998081468445437942925000000000000)
      constant := (236223322349088556565476583222390437247377084) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel007
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
  base := (11878827991292444567463759994369935394057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-2328147875777170716232733519550000000000000)
      constant := (8744782582046604411423975832269394300755851) }

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
  base := (5909335333335629257569072326113729090157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-564141770286127748024566928050912500000000000)
      constant := (2116852169527039891811793603919067202626545084) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel008
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
  base := (8166077384194026606818892031148494444383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-2548091211813748442893690125000000000000000)
      constant := (9151944680263694917493442229169084149985069) }

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
  base := (1014787129404518407217034743308394013669/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-617472341085272762833124914615500000000000000)
      constant := (2217154908823435668740071412922022346942553712) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel009
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
  base := (2685994041151452283427284859444011964693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (290)
      previous := (0)
      next := (250)
      square := (11376379450167813447980514075000000000000)
      linear := (-153779697102795898308591485025000000000000)
      constant := (550025510730404633762072970573738323046711) }

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
  base := (1333440221301360875431972640510942428939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-74533656876046419737964766797787500000000000)
      constant := (266667888065871371319900875718601413197749704) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel010
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
  base := (6419720273575732287060079849849664194867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-5975955767773807792431206671800000000000000)
      constant := (21841316066262770584427373089013468399352681) }

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
  base := (3179031104815062887958167414977163614607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-724133482683562792450240887744675000000000000)
      constant := (2648600075276861166404444953726701771020579242) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel011
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
  base := (1496286043787331083810044329579333482287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-3207921219923481622876559941350000000000000)
      constant := (12167973176777636569494993680025278036195741) }

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
  base := (294248246560682544044516421158833599317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5346000000000000000000000000000000000000000
      center := (23013)
      previous := (0)
      next := (19755)
      square := (901009252453290825080056714740000000000000)
      linear := (-14135710063321960131978161351077500000000000)
      constant := (53675791122809871313146895459135827546948682) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel012
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
  base := (44417714592443689583548016635003130761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (232)
      previous := (0)
      next := (200)
      square := (9101103560134250758384411260000000000000)
      linear := (-152349535820447082201667402080000000000000)
      constant := (605030702022165823545486961969145084530547) }

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
  base := (181153825938699318934392950754653467619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-92310513809094758007484095652650000000000000)
      constant := (367074499888347019348733875962184202878711273) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel013
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
  base := (-102669370061877744794723895366348596989/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 121500000000000000000000000000000000000000
      center := (522)
      previous := (0)
      next := (450)
      square := (20477483010302064206364925335000000000000)
      linear := (-364780789199663707619847315225000000000000)
      constant := (1523666954788109001615160272579727290931673) }

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
  base := (-2086988419370790455554263963052245868917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-884125195080997836875914847438437500000000000)
      constant := (3698370251330573719249435459784369736591233449) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel014
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
  base := (-3945309534788280977592205566924027143299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-7735502456066429605718859515400000000000000)
      constant := (34049735618806866640611383267137461404178343) }

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
  base := (-1986486026885215802425758330269981672471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-937455765880142851684472834003025000000000000)
      constant := (4133003218844149852170582608653410645268670374) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel015
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
  base := (-1383090491491628141423325001999484981261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (290)
      previous := (0)
      next := (250)
      square := (11376379450167813447980514075000000000000)
      linear := (-227094142448321807195577020175000000000000)
      constant := (1053790303181397765603377984914763905505953) }

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
  base := (-694396756140184864192637548429159627333/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-110087370742143096277003424507512500000000000)
      constant := (511696098159135010941214529204081655855024712) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel016
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
  base := (-6871291292421805169337642772207489922647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-8615275800212740512362685937200000000000000)
      constant := (42119695559703696806912886806353579948796779) }

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
  base := (-275604656049051002901881126758317271059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-208823381495686576260317761426440000000000000)
      constant := (1022698665770438635201848233470725986395261115) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel017
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
  base := (-320151291288760856454186075741798202347/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-1811032494457179193136919829620000000000000)
      constant := (9317868031137447351767534546628715184148395) }

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
  base := (-8019316203798413276787687606174580480781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1097447478277577896110146793696787500000000000)
      constant := (5656467827997623304075328471570109356998596257) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel018
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
  base := (-8960927201769213752620591077677855825951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-1055005460484339046556279151000000000000000)
      constant := (5704203253527005963278114795202697892699323) }

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
  base := (-8973737503360423793351863316985136479823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-127864227675191434546522753362375000000000000)
      constant := (692586438334289280580664571262889246620418259) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel019
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
  base := (-9766204976757091601947307735302436060711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-9934935816432206872328425569900000000000000)
      constant := (56359457558929763152567689156596508037247227) }

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
  base := (-9776758804329358423194146517161976098489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1204108619875867925727262766825962500000000000)
      constant := (6843236281719759265357731331223956338651127933) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel020
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
  base := (-1043751803867856032973057294616603978937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 243000000000000000000000000000000000000000
      center := (1044)
      previous := (0)
      next := (900)
      square := (40954966020604128412729850670000000000000)
      linear := (-1037482248850536232565033878080000000000000)
      constant := (6164987469639386020302546836008165233118309) }

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
  base := (-5223101101637054502695841542380664470867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1257439190675012940535820753390550000000000000)
      constant := (7485818815025675397726193720891481395126195198) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel021
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
  base := (-1373577397195715833338463434577353543933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (145)
      previous := (0)
      next := (125)
      square := (5688189725083906723990257037500000000000)
      linear := (-150204293896923858041281277662500000000000)
      constant := (933413038418854762295933358625786454313809) }

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
  base := (-10995755117830601317098789548626914617107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-145641084608239772816042082217237500000000000)
      constant := (906735899309511421856188882385665166820911431) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel022
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
  base := (-1143013352613120693816766972941944327517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 243000000000000000000000000000000000000000
      center := (1044)
      previous := (0)
      next := (900)
      square := (40954966020604128412729850670000000000000)
      linear := (-1125459583265167323229416520260000000000000)
      constant := (7302446786097164543236767264765107528413369) }

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
  base := (-1429498601442839251461115522171697337113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26730000000000000000000000000000000000000000
      center := (115065)
      previous := (0)
      next := (98775)
      square := (4505046262266454125400283573700000000000000)
      linear := (-124009121115754815468448793319975000000000000)
      constant := (806121662830687345295555472680944486643175608) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel023
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
  base := (-5885152452727686622434736043549961900751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-5847241252362414342808039206750000000000000)
      constant := (39552029366156818711861220415454859258117507) }

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
  base := (-11775102339388258151753685613481754878591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1417430903072447984961494713084312500000000000)
      constant := (9605723330268036823689043720064837758179788827) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel024
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
  base := (-12015549846273573937722139839948668003297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-1348263241866442682104221291600000000000000)
      constant := (9493661351468314356677845913921385963910981) }

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
  base := (-6009737421370410798198447533380246213623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-163417941541288111085561411072100000000000000)
      constant := (1152843405031469252133141205351368471240187318) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel025
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
  base := (-97366994779853506580488983565140583647/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-2514851169774227918451980967060000000000000)
      constant := (18407986339188704424036835098216770954344475) }

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
  base := (-608704050766368382590699744961753011949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-304818408934147602915722137242697500000000000)
      constant := (2235358793052693246537345398402439164133654212) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel026
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
  base := (-12240190699064182160934663434247002693717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-13014142520944295045581818046200000000000000)
      constant := (98894046644033490973916904814977978345426769) }

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
  base := (-12242806920000181770281901136566320843171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1577422615469883029387168672778075000000000000)
      constant := (12009219028302719965001113989711970155748243087) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel027
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
  base := (-2445312061882221210689977107203910615883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (232)
      previous := (0)
      next := (200)
      square := (9101103560134250758384411260000000000000)
      linear := (-298978426511498899975638472380000000000000)
      constant := (2355656735227687855007806000200494413371159) }

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
  base := (-12228692006439362800368425687019913381837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-181194798474336449355080739926962500000000000)
      constant := (1430308496162448946632999163080322739856538521) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel028
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
  base := (-6066190491622821148848427666377911866107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-6946957932545302976112822234000000000000000)
      constant := (56685434176516588163086442507670167416535999) }

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
  base := (-6067057860531412381396701257335238634463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1684083757068173059004284645907250000000000000)
      constant := (13767396313878401970823137147999312706861768822) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel029
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
  base := (-11959532037926303183342951900406312298763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-14333802537163761405547557678900000000000000)
      constant := (120992535773277041039992576718476266111400591) }

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
  base := (-5980471031363311577358482613237507820193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1737414327867318073812842632471837500000000000)
      constant := (14693023766393439718596548622095837537000730442) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel030
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
  base := (-11709487144912017521717631604545490887079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-1641521023248546317652163432200000000000000)
      constant := (14318799693757003101739698580177271746048867) }

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
  base := (-2927657987244785928545215724433619219597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-198971655407384787624600068781825000000000000)
      constant := (1738846207516497619684620593550156151538306404) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel031
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
  base := (-11383402302821490173524676082281043402767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-15213575881310072312191384100700000000000000)
      constant := (137000571856976791672015997586880706453127619) }

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
  base := (-2846082696080987903368565932926358558703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1844075469465608103429958605601012500000000000)
      constant := (16637138939314900219757428894885663164068822764) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel032
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
  base := (-10982184554155138634245210565657504550747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-15653462553383227765513297311600000000000000)
      constant := (145386439201440730857666794382945226394168479) }

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
  base := (-2745734207918391253324944254226687050641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-1897406040264753118238516592165600000000000000)
      constant := (17655566569768287874904940459988290882600010708) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel033
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
  base := (-10506545736207307144760079021188916601789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-1788149913939598135426134502500000000000000)
      constant := (17114069588971368869119514725102899251751697) }

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
  base := (-10507154669057209958788763329167517841849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (12785)
      previous := (0)
      next := (10975)
      square := (500560695807383791711142619300000000000000)
      linear := (-19704410212766647808556308876062500000000000)
      constant := (188938162043442911204031541840890762825970847) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel034
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
  base := (-4978522284436693483118216636236978128433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-8266617948764769336078561866700000000000000)
      constant := (81460498692973489244389447061344414314790781) }

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
  base := (-622346064207882564822246470327855160347/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2004067181863043147855632565294775000000000000)
      constant := (19785057104967362372072101004314093383025074544) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel035
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
  base := (-9334119634854363667317884772036392914671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-16973122569602694125479036944300000000000000)
      constant := (172069445881458367364596181590270156521734947) }

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
  base := (-9334517558408927994295747758414696620483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2057397752662188162664190551859362500000000000)
      constant := (20896091007100172863105341616389315097142938351) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel036
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
  base := (-8638115237280193058388827153774603476697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-1934778804630649953200105572800000000000000)
      constant := (20163543124623989687511565252848085706129181) }

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
  base := (-4319218256969803148761598054065757433097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-234525369273481464163638726491550000000000000)
      constant := (2448663304920053989070375660341953090932144202) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel037
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
  base := (-491831355067889802690403939879923363939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-2231611989218625629015357920762500000000000)
      constant := (23891032302790038132978561367752732245125646) }

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
  base := (-1967390219001475294681735935192866657063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2164058894260478192281306524988537500000000000)
      constant := (23210685466433975514602996856521947738604506444) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel038
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
  base := (-7027891185300019240171595817967244372277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-18292782585822160485444776577000000000000000)
      constant := (201038505214347872608081357364933959617536689) }

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
  base := (-1405620028624646074191259185577719485919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-443477893011924641417972902310625000000000000)
      constant := (4882846402735158574881868126764584251455523643) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel039
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
  base := (-6114050370086781013060791807178377811477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-2081407695321701770974076643100000000000000)
      constant := (23466954223222050701653513436681183799090121) }

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
  base := (-6114218711712925341482578915269131272209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-252302226206529802433158055346412500000000000)
      constant := (2849844950250884619102248163263960670008693197) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel040
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
  base := (-5127910057371792379969105592009168004311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-19172555929968471392088602998800000000000000)
      constant := (221620475016544215521193303373141772174952427) }

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
  base := (-2564022794387539901776184394585700343629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2324050606657913236706980484682300000000000000)
      constant := (26913799288987657851685086286515868305592553026) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel041
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
  base := (-4069572963849019482423710018483125296343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-19612442602041626845410516209700000000000000)
      constant := (232292141276828516454625301692383600552988651) }

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
  base := (-2034841005921210538775757744868347473303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2377381177457058251515538471246887500000000000)
      constant := (28209813247177706932302593939453613755359943782) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel042
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
  base := (-36738996751346091783094188263849371137/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6750000000000000000000000000000000000000
      center := (29)
      previous := (0)
      next := (25)
      square := (1137637945016781344798051407500000000000)
      linear := (-55700914650318839718701192835000000000000)
      constant := (675604353310439381763270677511252133958602) }

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
  base := (-367400928448906982603957113194240172003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-270079083139578140702677384201275000000000000)
      constant := (3281849343428609485327836246594522526364529592) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel043
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
  base := (-434153427929302263412411287938423964057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 607500000000000000000000000000000000000000
      center := (2610)
      previous := (0)
      next := (2250)
      square := (102387415051510321031824626675000000000000)
      linear := (-5123053986546984438013585657875000000000000)
      constant := (63599184343304957770012131837799712976734149) }

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
  base := (-434171045731362090500157346748818198877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2484042319055348281132654444376062500000000000)
      constant := (30894289986840978839303186913997141665868678276) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel044
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
  base := (-231052300714961566714314128660049082231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-10466051309130546602688127921200000000000000)
      constant := (132914819869292329565282447578935608073017867) }

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
  base := (-115540301490804613294088359118078531397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26730000000000000000000000000000000000000000
      center := (115065)
      previous := (0)
      next := (98775)
      square := (4505046262266454125400283573700000000000000)
      linear := (-230670262714044845085564766449150000000000000)
      constant := (2934795408772247938860062982441865754342303276) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel045
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
  base := (884368548444141978671874427907042861371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-2374665476703805406522018783700000000000000)
      constant := (30835140533396813852840671390428490157257017) }

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
  base := (22108077637215654486401340202050844449/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6534000000000000000000000000000000000000000
      center := (28127)
      previous := (0)
      next := (24145)
      square := (1101233530776244341764513762460000000000000)
      linear := (-57571188014525295794439342611227500000000000)
      constant := (748933810906844828133914286507857910245519064) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel046
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
  base := (460555016314179680832142271248766981571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-4362375192481480822404016452840000000000000)
      constant := (57891321021938128872115723918613450376521753) }

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
  base := (287842327161978033825414261774483266359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2644034031452783325558328404069825000000000000)
      constant := (35152105083746898971016118929160758239346029416) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel047
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
  base := (474136365761294760827850116176764577673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-2781470329310069945667749434387500000000000)
      constant := (37706331852060080135986720195890328792374539) }

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
  base := (3793061680294789186187922539807275688687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2697364602251928340366886390634412500000000000)
      constant := (36632999579955015504628840022092913873949463861) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel048
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
  base := (66941214751862524705106432393797313631/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6750000000000000000000000000000000000000
      center := (29)
      previous := (0)
      next := (25)
      square := (1137637945016781344798051407500000000000)
      linear := (-63032359184871430607399746350000000000000)
      constant := (872495581466085860356796135269265054936074) }

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
  base := (5355273734473589202788548514600813497061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-305632797005674817241716041911000000000000000)
      constant := (4238300492634704004266727643667500857694898287) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel049
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
  base := (218418093790814751217781374104521208271/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-2891441997328358808998227737112500000000000)
      constant := (40849983129613543259980223853538969614439412) }

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
  base := (6989360213607029963843413422172207265913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2804025743850218369984002363763587500000000000)
      constant := (39687219216728141182665259265834464957114639939) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel050
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
  base := (4347662367262962840106442785322413771563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-11785711325350012962653867553900000000000000)
      constant := (169877509555829644495857550885583346546489809) }

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
  base := (8695309685666687210643259749052353592933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2857356314649363384792560350328175000000000000)
      constant := (41260543592866499178944143141905253540193008999) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel051
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
  base := (5236562613749089810043796067902888864861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (580)
      previous := (0)
      next := (500)
      square := (22752758900335626895961028150000000000000)
      linear := (-1333961629042954521034980462150000000000000)
      constant := (19609103851557350851500764871270877999351247) }

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
  base := (5236556589126283287984884629127778732653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-323409653938723155511235370765862500000000000)
      constant := (4762741922034659221428653356677531453114154702) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel052
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
  base := (12322773293041150849506055115914631244237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-24451195994846336831951561529600000000000000)
      constant := (366426413939542276114529630905567255392349591) }

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
  base := (12322763649219608174984107965476316676103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-2964017456247653414409676323457350000000000000)
      constant := (44499620126004251428612554234771518889227456509) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel053
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
  base := (113954106295926330786992275956528206669/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-4978216533383898457054694948100000000000000)
      constant := (76028530314931461537075958223050908855514175) }

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
  base := (14244255571245898425150668352555283063669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3017348027046798429218234310021937500000000000)
      constant := (46165371913423608261140870748070021659796059607) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel054
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
  base := (2029698847095737096319853348609970481057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (145)
      previous := (0)
      next := (125)
      square := (5688189725083906723990257037500000000000)
      linear := (-351819018597120107480491499325000000000000)
      constant := (5473785849392502463659083352299969202988539) }

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
  base := (16237584605817104807564127360684065476091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-341186510871771493780754699620725000000000000)
      constant := (5317992503667185174598828504010572029410389297) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel055
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
  base := (3660550456226056265757033822163108391627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-5154171202213160638383460232460000000000000)
      constant := (81667240367682098412488874554960635339165361) }

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
  base := (18302747347380906783566673219901718920833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26730000000000000000000000000000000000000000
      center := (115065)
      previous := (0)
      next := (98775)
      square := (4505046262266454125400283573700000000000000)
      linear := (-284000833513189859894122753013737500000000000)
      constant := (4508118353146724679869105087215885185300386609) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel056
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
  base := (5109936266464339754956343799650158260067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 607500000000000000000000000000000000000000
      center := (2610)
      previous := (0)
      next := (2250)
      square := (102387415051510321031824626675000000000000)
      linear := (-6552685670784739661309803593300000000000000)
      constant := (105703378239172797830891644395314988457196281) }

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
  base := (4087948224513591949332833193141308048351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-635467947888846694728781653943140000000000000)
      constant := (10269495977929288828637644364106508880545664453) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel057
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
  base := (113242834916441233317692481632128415343/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6750000000000000000000000000000000000000
      center := (29)
      previous := (0)
      next := (25)
      square := (1137637945016781344798051407500000000000)
      linear := (-74029525986700316940447576622500000000000)
      constant := (1215401427747836573761239903457212336071305) }

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
  base := (2831070479078362698445585985444613802087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-358963367804819832050274028475587500000000000)
      constant := (5904051831821388696130460429223100348206345832) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel058
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
  base := (6232304086588573640331051546213662763171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 607500000000000000000000000000000000000000
      center := (2610)
      previous := (0)
      next := (2250)
      square := (102387415051510321031824626675000000000000)
      linear := (-6772629006821317387970760198750000000000000)
      constant := (113132301131510683969280964117904920051450553) }

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
  base := (997168553190883570053365653126065944947/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-656800176208504700652204848568975000000000000)
      constant := (10991252325280458516354738962747204522396383205) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel059
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
  base := (3410211478707565144199149499535190996097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-3441300337419803125650619250737500000000000)
      constant := (58470948030635614846727356153671426412051571) }

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
  base := (27281689820144785549263156154046957536073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3337331451841668518069582229409462500000000000)
      constant := (56806865271632498643427253062330418864308154419) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel060
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
  base := (1485299619590842557420122976812915653323/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (58)
      previous := (0)
      next := (50)
      square := (2275275890033562689596102815000000000000)
      linear := (-155390496507953224769593706760000000000000)
      constant := (2684775849407166260823273294473948722639721) }

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
  base := (3713248848457452099500706615431055460083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-376740224737868170319793357330450000000000000)
      constant := (6520919710245239800851620870564624815504729288) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel061
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
  base := (32202117214452818533843056746840779927999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-28410176043504735911848780427700000000000000)
      constant := (499005410271793737159341015365357309522503757) }

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
  base := (32202115934241051319447701849106544427303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3443992593439958547686698202538637500000000000)
      constant := (60600497964660456416730533254455137147670990109) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel062
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
  base := (54328227584893588247137264577636110809/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 60750000000000000000000000000000000000000
      center := (261)
      previous := (0)
      next := (225)
      square := (10238741505151032103182462667500000000000)
      linear := (-721251567889447284129267340965000000000000)
      constant := (12875121405607246834678994042575349198825392) }

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
  base := (34770064632922199585402553155378138288253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3497323164239103562495256189103225000000000000)
      constant := (62543526970557685817651396316797725587589502959) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel063
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
  base := (9352459301437871335551303456736922371093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (290)
      previous := (0)
      next := (250)
      square := (11376379450167813447980514075000000000000)
      linear := (-813609705212529078291461301375000000000000)
      constant := (14757166406330350108870186875500646904019511) }

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
  base := (2338114774439845678915173628877470339731/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-394517081670916508589312686185312500000000000)
      constant := (7168596043934777978926321881520496801473418832) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel064
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
  base := (40121431471019076664037748190475435866607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-29729836059724202271814520060400000000000000)
      constant := (547764813385962649199595984112685530915585501) }

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
  base := (20060715410668482600777949243288042121423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3603984305837393592112372162232400000000000000)
      constant := (66522010227840090294028579412055196604992400938) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel065
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
  base := (8580969627453948575867146363428777892687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-6033944546359471545027286654260000000000000)
      constant := (112905064884494766365967081876088193027922941) }

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
  base := (8580969523863282043105798110797129769017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-731462975327307721384186029759397500000000000)
      constant := (13711492891777123488056572790242642615973406851) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel066
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
  base := (35750067936142793105848676611970070559/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 6750000000000000000000000000000000000000
      center := (29)
      previous := (0)
      next := (25)
      square := (1137637945016781344798051407500000000000)
      linear := (-85026692788529203273495406895000000000000)
      constant := (1615387565771082387690500218530242140962976) }

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
  base := (22880043272713387548568646732205290371637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (12785)
      previous := (0)
      next := (10975)
      square := (500560695807383791711142619300000000000000)
      linear := (-37481267145814986078075637730925000000000000)
      constant := (713370980621273952849384245549094004980752378) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel067
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
  base := (48687147740087908065148954886453001445281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-31049496075943668631780259693100000000000000)
      constant := (598807411104189937902406246585683079351203283) }

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
  base := (24343573705555736451860502892740975324401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3763976018234828636538046121926162500000000000)
      constant := (72720798090157472643572082344980533216801725206) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel068
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
  base := (12921507582485331651766749666692539384091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 607500000000000000000000000000000000000000
      center := (2610)
      previous := (0)
      next := (2250)
      square := (102387415051510321031824626675000000000000)
      linear := (-7872345687004206021275543226000000000000000)
      constant := (154082246666285834950147134994306287070334113) }

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
  base := (12921507516962104234338427351867140994829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3817306589033973651346604108490750000000000000)
      constant := (74848677480472676459552859586393466936683828348) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel069
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
  base := (10951346921462410779761517616567276552247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (232)
      previous := (0)
      next := (200)
      square := (9101103560134250758384411260000000000000)
      linear := (-709539320446443989742757469220000000000000)
      constant := (14091205562914793286129683921342316466910669) }

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
  base := (13689183599637467333286685629055892435839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-430070795537013185128351343895037500000000000)
      constant := (8556373916556555780398894523364194199226544052) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel070
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
  base := (57899260477060964966881768773129097026981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-32369156092163134991745999325800000000000000)
      constant := (652133202079138204759590140125370370577556383) }

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
  base := (57899260310812679481384452577377582683097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3923967730632263680963720081619925000000000000)
      constant := (79196861393049519498306186385165312751131101091) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel071
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
  base := (15278401965996473332627419180593955409549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 607500000000000000000000000000000000000000
      center := (2610)
      previous := (0)
      next := (2250)
      square := (102387415051510321031824626675000000000000)
      linear := (-8202260691059072611266978134175000000000000)
      constant := (167603960472696683499255531004103081164520407) }

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
  base := (61113607731620672870612685777133201868633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-3977298301431408695772278068184512500000000000)
      constant := (81417165910447334304540980126469076831418416099) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel072
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
  base := (32199888354276812417990627514732703509507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (580)
      previous := (0)
      next := (500)
      square := (22752758900335626895961028150000000000000)
      linear := (-1847162746461635883243879208200000000000000)
      constant := (38275120541758039697154454683697782994756689) }

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
  base := (8049972075398333140944871111035604444367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-447847652470061523397870672749900000000000000)
      constant := (9296475422167036651129677933765501557757975912) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel073
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
  base := (67757766963548142210294395924022615363181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-33688816108382601351711738958500000000000000)
      constant := (707742185650238654217524808807612495533252983) }

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
  base := (13551553375937768282827148422058994596601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-816791888605939745077878808262737500000000000)
      constant := (17190040011774041468700052339322283977498859203) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel074
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
  base := (14237515718287664601510578022310032850103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-6825740556091151361006730433880000000000000)
      constant := (145357177915489698049780643732201337982575029) }

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
  base := (71187578524709028792813709563699165845841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4137290013828843740197952027878275000000000000)
      constant := (88262929687477163215658287117890901260865262923) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel075
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
  base := (14937842312462113476661972536593055258331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (232)
      previous := (0)
      next := (200)
      square := (9101103560134250758384411260000000000000)
      linear := (-768190876722864716852345897340000000000000)
      constant := (16579628478355671508460329405863012491974937) }

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
  base := (74689211509221814878971414673952942886299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-465624509403109861667390001604762500000000000)
      constant := (10067385298274529252921794775562958561284538833) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel076
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
  base := (78262665852245024879127213171298064532249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-35008476124602067711677478591200000000000000)
      constant := (765634361490096313451559164202625429681336507) }

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
  base := (39131332905007987765413144727960201967329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4243951155427133769815068001007450000000000000)
      constant := (92980814049168527901973026436671646386890749174) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel077
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
  base := (8190794144204015187975067055950356832839/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 243000000000000000000000000000000000000000
      center := (1044)
      previous := (0)
      next := (900)
      square := (40954966020604128412729850670000000000000)
      linear := (-3544836279667522316499939180210000000000000)
      constant := (78543912946505580186292945362023436710379877) }

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
  base := (5119246338028449162257303923810782123947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26730000000000000000000000000000000000000000
      center := (115065)
      previous := (0)
      next := (98775)
      square := (4505046262266454125400283573700000000000000)
      linear := (-390661975111479889511238726142912500000000000)
      constant := (8671451707365681204876360313828261795501965296) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel078
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
  base := (85625038316210795313291518302497540282439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-3987583274305375402035700557000000000000000)
      constant := (89499731716346754546484081488467433587625853) }

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
  base := (1070312978618812698587764448994402910449/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6534000000000000000000000000000000000000000
      center := (28127)
      previous := (0)
      next := (24145)
      square := (1101233530776244341764513762460000000000000)
      linear := (-96680273267231639987381866091925000000000000)
      constant := (2173820708435346709370631875239981366434990128) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel079
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
  base := (44706978231100533081110816058568116838199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-18164068070410767035821609111950000000000000)
      constant := (412904864716620099793290834664869552391682357) }

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
  base := (22353489110242225870107559348806716946757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4403942867824568814240741960701212500000000000)
      constant := (100288703344514238454669267325534941140416984284) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel080
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
  base := (11659336983720735343744426428663745310739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-4596002851611836190620641429350000000000000)
      constant := (105796945177615559127524245060165290110509577) }

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
  base := (93274695852888168642483841915665398738639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4457273438623713829049299947265800000000000000)
      constant := (102786283175500587762994768890927809719112202517) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel081
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
  base := (97207256530484970021187409397058518953547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-4134212164996427219809671627300000000000000)
      constant := (96355009045347498264528264807595580011745769) }

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
  base := (24301814129267689505972373075823060345487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-501178223269206538206428659314487500000000000)
      constant := (11701630152478753211336188041725056924469824116) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel082
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
  base := (101211638437380879323832345074130688932181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-37647796157041000431608957856600000000000000)
      constant := (888268289393153713645806214420913757410519983) }

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
  base := (50605819213360521735511142488288516469529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4563934580222003858666415920394975000000000000)
      constant := (107873867934739000017161004739320311687007122374) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel083
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
  base := (105287841584618700644550616369643053754211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-38087682829114155884930871067500000000000000)
      constant := (909595185374585277682107930630898262062273273) }

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
  base := (105287841576148937107637349540697053695133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4617265151021148873474973906959562500000000000)
      constant := (110463872862623945454575478058093235391672995599) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel084
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
  base := (54717932983634967385120393825151324854727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (580)
      previous := (0)
      next := (500)
      square := (22752758900335626895961028150000000000000)
      linear := (-2140420527843739518791821348800000000000000)
      constant := (51731987186179141732270882391079085771077629) }

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
  base := (10943586596054126804143950444599096709301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6534000000000000000000000000000000000000000
      center := (28127)
      previous := (0)
      next := (24145)
      square := (1101233530776244341764513762460000000000000)
      linear := (-103791016040450975295189597633870000000000000)
      constant := (2512993025684935412233843491305324247898572734) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel085
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
  base := (7103481973820422391511049640385024441479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-4870932021657558348946837186162500000000000)
      constant := (119126255165256129130873204741461496878558794) }

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
  base := (113655711575782035201284137944744242797209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4723926292619438903092089880088737500000000000)
      constant := (115736307814212421525508576872041328642841336227) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel086
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
  base := (117947378422555870737943358661741064499077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-39407342845333622244896610700200000000000000)
      constant := (975098001286175831286052282876303078673275711) }

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
  base := (117947378418311031058132283951173510701423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-4777256863418583917900647866653325000000000000)
      constant := (118418737837690248597556004628178159422653940469) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel087
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
  base := (24462173297676687082951354663060106618227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (232)
      previous := (0)
      next := (200)
      square := (9101103560134250758384411260000000000000)
      linear := (-885493989275706171071522753580000000000000)
      constant := (22165325538729637856918163931797622878692129) }

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
  base := (122310866485012591340072877367375248904739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-536731937135303214745467317024212500000000000)
      constant := (13459108469573773876675359925564047360046782313) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel088
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
  base := (15843271971975555854827217073021626367557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-5035889523684991643942554640250000000000000)
      constant := (127504373148917629193371636225144255207316351) }

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
  base := (25349235154625599947909288797146802362077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5346000000000000000000000000000000000000000
      center := (23013)
      previous := (0)
      next := (19755)
      square := (901009252453290825080056714740000000000000)
      linear := (-88798509182124980863959342541500000000000000)
      constant := (2252291326900953743045165631956538402713831821) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel089
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
  base := (13125330628231129090384486241531661785907/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 243000000000000000000000000000000000000000
      center := (1044)
      previous := (0)
      next := (900)
      square := (40954966020604128412729850670000000000000)
      linear := (-4072700286155308860486235033290000000000000)
      constant := (104288400913108847101533884467619693813975401) }

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
  base := (5250132251207458749325787626603937700487/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58806000000000000000000000000000000000000000
      center := (253143)
      previous := (0)
      next := (217305)
      square := (9911101776986199075880623862140000000000000)
      linear := (-987449715163203792465264365269417500000000000)
      constant := (25330175619556614592844568373509688760412096305) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel090
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
  base := (135832258005637386267381835872824919342423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-4574098837069582673131584838200000000000000)
      constant := (118442969006836137411116884114066272822245421) }

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
  base := (135832258003950710158775947900987079211487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-554508794068351553014986645879075000000000000)
      constant := (14384060175643337021829383811272516975283928029) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel091
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
  base := (70241515471856339350515421385615326029483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-20803388102849699755753088377350000000000000)
      constant := (544671560491074153711830179002642024225164369) }

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
  base := (70241515471186983301946658079437348055853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-5043909717414308991943437799476262500000000000)
      constant := (132293013428513155756007830572308593861647491518) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel092
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
  base := (9075351568414278305965209908363842645753/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-5255832859721569370603511245700000000000000)
      constant := (139119151111561733170749044517514827525835958) }

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
  base := (145205625093566047555323081091664754994351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-5097240288213454006751995786040850000000000000)
      constant := (135160293640896863371194123957168587541098902453) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel093
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
  base := (15000004045660947035654729254955939128217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (116)
      previous := (0)
      next := (100)
      square := (4550551780067125379192205630000000000000)
      linear := (-472072772776063449090555590850000000000000)
      constant := (12631299831023672528588760371251310356461859) }

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
  base := (15000004045576644235782058647909504338049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6534000000000000000000000000000000000000000
      center := (28127)
      previous := (0)
      next := (24145)
      square := (1101233530776244341764513762460000000000000)
      linear := (-114457130200279978256901194946787500000000000)
      constant := (3067964049286430927716159462870850310719812166) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel094
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
  base := (154866277027991869306386923533517602853427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2430000000000000000000000000000000000000000
      center := (10440)
      previous := (0)
      next := (9000)
      square := (409549660206041284127298506700000000000000)
      linear := (-42926436221918865871471916387400000000000000)
      constant := (1160934448680653975632605349550544777493382761) }

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
  base := (154866277027322996489287353052004260298037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-5203901429811744036369111759170025000000000000)
      constant := (140987279159442162584693724602416473453043181911) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel095
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
  base := (6392173392288223920607388062016100960609/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 486000000000000000000000000000000000000000
      center := (2088)
      previous := (0)
      next := (1800)
      square := (81909932041208256825459701340000000000000)
      linear := (-8673264578798404264958765919660000000000000)
      constant := (237061120111536537394901431983924562667139935) }

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
  base := (159804334806674962942434285979984975881477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-5257232000610889051177669745734612500000000000)
      constant := (143946984465509285239338449021554746292718068231) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel096
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
  base := (164814213792760416458869836505730969502273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1160)
      previous := (0)
      next := (1000)
      square := (45505517800671253791922056300000000000000)
      linear := (-4867356618451686308679526978800000000000000)
      constant := (134436715602539392585871629169654736176561371) }

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
  base := (164814213792339495798483652516361911407269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (140635)
      previous := (0)
      next := (120725)
      square := (5506167653881221708822568812300000000000000)
      linear := (-590062507934448229554025303588800000000000000)
      constant := (16326388681783017732512391934516954364567547823) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel097
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
  base := (5309247311976084627865646675783938284767/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 303750000000000000000000000000000000000000
      center := (1305)
      previous := (0)
      next := (1125)
      square := (51193707525755160515912313337500000000000)
      linear := (-5530762029767291528929707002512500000000000)
      constant := (154351121034478007713375330015271363012793524) }

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
  base := (5309247311965651670320446266682796990133/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-5363893142209179080794785718863787500000000000)
      constant := (149958820171014158594037011765651425003703179168) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell179.Kernel098
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
  base := (87524717688633252999010603389784761038793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1215000000000000000000000000000000000000000
      center := (5220)
      previous := (0)
      next := (4500)
      square := (204774830103020642063649253350000000000000)
      linear := (-22342991455105743842379784615500000000000000)
      constant := (629970592058130157158238334318067696932426699) }

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
  base := (175049435377001736199854609237900374665599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294030000000000000000000000000000000000000000
      center := (1265715)
      previous := (0)
      next := (1086525)
      square := (49555508884930995379403119310700000000000000)
      linear := (-5417223713008324095603343705428375000000000000)
      constant := (153010950570370373560597796524509176903792607397) }

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
end ForestUnimodality.Stage80KernelData.Cell179.Kernel098
